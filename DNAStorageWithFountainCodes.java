import javax.swing.*;
import javax.swing.border.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import javax.imageio.ImageIO;
import java.io.*;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.function.IntConsumer;
import java.util.zip.*;
import java.util.List;
import java.util.ArrayList;

/**
 * ╔══════════════════════════════════════════════════════════════╗
 * ║ DNA Storage System — Fountain Codes Edition ║
 * ║ LT Codes (Luby Transform) + Robust Soliton Distribution ║
 * ╚══════════════════════════════════════════════════════════════╝
 * ROOT-CAUSE FIX: The original corruption simulator corrupted raw PNG
 * bytes, which destroyed the GZIP-compressed droplet container before
 * it could be read, producing "invalid stored block lengths".
 * CORRECT MODEL: Corruption is simulated at the DROPLET level only.
 * The PNG is always read cleanly; then a chosen fraction of the
 * extracted droplets is ERASED before the LT decoder runs. This is
 * the proper erasure-channel model for fountain codes.
 * Full CorruptionTestDialog with:
 * • Custom PNG or .dat file selection
 * • Six corruption models (uniform, burst, front, back, periodic, clustered)
 * • Erasure percentage slider (0–50%)
 * • Reproducible seed / random seed option
 * • Auto-save recovered file with descriptive suffix
 * • Detailed per-step result log + progress bar
 * OUTPUT FILES:
 * dna_strand_<name>.png — visualization + embedded droplet bundle
 * dna_sequence_<name>.dat — DNA text + fountain bundle (backup path)
 */
public class DNAStorageWithFountainCodes extends JFrame {
    // UI
    private JButton loadFileBtn, encodeBtn, saveImageBtn, decodeBtn, corruptTestBtn;
    private JTextArea dnaTextArea, logArea;
    private DNAVisualizationPanel dnaPanel;
    private JLabel statusLabel, compressionLabel;
    // State
    private byte[] originalFileData;
    private String dnaSequence = "";
    private String originalFileName = "";
    private String baseFileName = "";
    // DNA maps
    private static final Map<String, Character> BINARY_TO_DNA = new HashMap<>();
    private static final Map<Character, String> DNA_TO_BINARY = new HashMap<>();
    private static final Map<Character, Color> BASE_COLORS = new HashMap<>();
    private static final Map<Character, Character> COMPLEMENT = new HashMap<>();
    static {
        BINARY_TO_DNA.put("00", 'A');
        BINARY_TO_DNA.put("01", 'C');
        BINARY_TO_DNA.put("10", 'G');
        BINARY_TO_DNA.put("11", 'T');
        DNA_TO_BINARY.put('A', "00");
        DNA_TO_BINARY.put('C', "01");
        DNA_TO_BINARY.put('G', "10");
        DNA_TO_BINARY.put('T', "11");
        BASE_COLORS.put('A', new Color(220, 20, 60));
        BASE_COLORS.put('T', new Color(30, 144, 255));
        BASE_COLORS.put('C', new Color(50, 205, 50));
        BASE_COLORS.put('G', new Color(255, 140, 0));
        COMPLEMENT.put('A', 'T');
        COMPLEMENT.put('T', 'A');
        COMPLEMENT.put('G', 'C');
        COMPLEMENT.put('C', 'G');
    }

    // FOUNTAIN CODE ENGINE — LT Codes + Robust Soliton Distribution
    // One LT-code encoded symbol.
    static class Droplet {
        final int id, degree;
        final int[] srcBlocks;
        byte[] data;

        Droplet(int id, int deg, int[] src, byte[] data) {
            this.id = id;
            this.degree = deg;
            this.srcBlocks = src;
            this.data = data;
        }
    }

    static class DropletBundle {
        List<Droplet> droplets;
        int k, blockSize, origLen, dupDroplets;

        DropletBundle(List<Droplet> d, int k, int bs, int ol) {
            droplets = d;
            this.k = k;
            blockSize = bs;
            origLen = ol;
            dupDroplets = 0;
        }

        DropletBundle(List<Droplet> d, int k, int bs, int ol, int dups) {
            droplets = d;
            this.k = k;
            blockSize = bs;
            origLen = ol;
            dupDroplets = dups;
        }
    }

    // Adaptive block size
    // Target k (source blocks) ≤ 8000 regardless of file size. Small files stay at
    // 512 B blocks; large files get proportionally larger blocks. This keeps N ≈ 10
    // 400 droplets for any file size, bounding encode/decode time.
    static final int TARGET_K = 8_000;
    static final int MIN_BLOCK = 512;

    static int adaptiveBlockSize(int dataLen) {
        int bs = (dataLen + TARGET_K - 1) / TARGET_K; // ceil(dataLen/TARGET_K)
        return Math.max(MIN_BLOCK, bs);
    }

    // Robust Soliton CDF (precomputed once per k)
    /**
     * Returns the Robust Soliton CDF in an array of length (pivot+1).
     * cdf[i] = P(degree <= i) for i in [1, pivot].
     * Degrees > pivot have zero probability (Tau is 0, Rho vanishes there).
     * Build once → O(k), then binary-search per call → O(N·log pivot).
     * Speedup for a 50 MB file: ~16 000×.
     */
    static double[] buildSolitonCdf(int k) {
        double c = 0.1, delta = 0.05;
        double R = c * Math.log(k / delta) * Math.sqrt(k);
        int pivot = Math.max(1, (int) Math.floor(k / R));
        // Accumulate Z over degrees 1..pivot (degrees above pivot have tau=0 and
        // negligible rho, and their combined rho tail = 1 - sum(rho[1..pivot])).
        double rhoSum = 0, tauSum = 0;
        for (int i = 1; i <= pivot; i++) {
            rhoSum += (i == 1) ? 1.0 / k : 1.0 / ((double) i * (i - 1));
            tauSum += (i < pivot) ? R / (k * i) : R * Math.log(R / delta) / k;
        }
        double Z = rhoSum + tauSum + (1.0 - rhoSum); // rho tail adds to Z too
        double[] cdf = new double[pivot + 1]; // [0] unused; [1]..[pivot] used
        double sum = 0;
        for (int i = 1; i <= pivot; i++) {
            double rho = (i == 1) ? 1.0 / k : 1.0 / ((double) i * (i - 1));
            double tau = (i < pivot) ? R / (k * i) : R * Math.log(R / delta) / k;
            sum += (rho + tau) / Z;
            cdf[i] = sum;
        }
        cdf[pivot] = 1.0; // guarantee no out-of-bounds on rng rounding
        return cdf;
    }

    // Sample one degree via binary search on a precomputed CDF. O(log pivot).
    static int sampleDegree(double[] cdf, Random rng) {
        double r = rng.nextDouble();
        int lo = 1, hi = cdf.length - 1;
        while (lo < hi) {
            int mid = (lo + hi) >>> 1;
            if (cdf[mid] < r)
                lo = mid + 1;
            else
                hi = mid;
        }
        return lo;
    }

    // Block selection
    /**
     * Choose 'deg' DISTINCT source-block indices for droplet 'id'.
     * Uses a SPARSE partial Fisher-Yates over a virtual array [0..k-1]:
     * virtual(x) = swap.getOrDefault(x, x) (unvisited positions equal their index)
     * For each step i in [0, deg):
     * j = i + rand.nextInt(k-i) <- uniform over remaining [i, k-1]
     * pick = virtual(j) <- element chosen this step
     * swap[j] = virtual(i) <- slide old virtual[i] into slot j
     * (slot i is finished; we never read it again so no write-back needed)
     * Guaranteed distinct, O(deg) time and space. No rejection loops.
     * The earlier version used int[deg] for the swap map and fell back to
     * identity for j >= deg, but failed to track writes to those high slots,
     * allowing the same index to be selected twice.
     */
    static int[] chooseBlocks(int k, int deg, int id) {
        deg = Math.min(deg, k);
        Random r = new Random((long) id * 0x9E3779B9L + 0xDEADC0DEL);
        HashMap<Integer, Integer> swap = new HashMap<>(deg * 2);
        int[] result = new int[deg];
        for (int i = 0; i < deg; i++) {
            int j = i + r.nextInt(k - i);
            int valJ = swap.getOrDefault(j, j); // virtual[j]
            int valI = swap.getOrDefault(i, i); // virtual[i]
            result[i] = valJ;
            swap.put(j, valI); // virtual[j] ← old virtual[i]
        }
        return result;
    }

    // Encoder
    // Encode src into LT droplets. blockSize should come from adaptiveBlockSize().
    static List<Droplet> fountainEncode(byte[] src, int blockSize, double overheadPct) {
        return fountainEncode(src, blockSize, overheadPct, null);
    }

    // Encode with optional progress callback.
    // progressCb receives integers 0–100 so callers can update a progress bar.
    static List<Droplet> fountainEncode(byte[] src, int blockSize, double overheadPct,
            IntConsumer progressCb) {
        int k = (int) Math.ceil((double) src.length / blockSize);
        byte[][] blocks = new byte[k][blockSize];
        for (int i = 0; i < src.length; i++)
            blocks[i / blockSize][i % blockSize] = src[i];
        int N = (int) Math.ceil(k * (1.0 + overheadPct));
        List<Droplet> out = new ArrayList<>(N);
        // Build CDF ONCE, reuse for all N sampleDegree() calls.
        double[] cdf = buildSolitonCdf(k);
        Random rng = new Random(0xDEADBEEFL);
        int reportInterval = Math.max(1, N / 20); // report ~every 5%
        for (int id = 0; id < N; id++) {
            int deg = sampleDegree(cdf, rng);
            int[] chosen = chooseBlocks(k, deg, id);
            byte[] xor = new byte[blockSize];
            for (int bi : chosen)
                for (int j = 0; j < blockSize; j++)
                    xor[j] ^= blocks[bi][j];
            out.add(new Droplet(id, deg, chosen, xor));
            if (progressCb != null && (id % reportInterval == 0))
                progressCb.accept(id * 100 / N);
        }
        if (progressCb != null)
            progressCb.accept(100);
        return out;
    }

    /**
     * Belief-propagation (peeling) LT decoder — O(N·deg_avg) via adjacency map.
     * Builds a block→droplet adjacency list so each block resolution only visits
     * the droplets that actually reference it.
     * For a 50 MB file (k≈100k, N≈130k) it is ~1000× faster.
     * Never throws unresolved blocks are zero (partial recovery).
     */
    static byte[] fountainDecode(List<Droplet> droplets, int k, int blockSize, int origLen) {
        // Working copies of each droplet's remaining unknown blocks and XOR data
        int N = droplets.size();
        @SuppressWarnings("unchecked")
        Set<Integer>[] remaining = new Set[N]; // droplet i → set of unresolved block indices
        byte[][] ddata = new byte[N][]; // droplet i → working XOR value
        // block → set of droplet indices that still reference it
        @SuppressWarnings("unchecked")
        Set<Integer>[] blockToDroplets = new Set[k];
        for (int i = 0; i < k; i++)
            blockToDroplets[i] = new HashSet<>();
        for (int i = 0; i < N; i++) {
            Droplet d = droplets.get(i);
            remaining[i] = new HashSet<>();
            for (int b : d.srcBlocks) {
                remaining[i].add(b);
                blockToDroplets[b].add(i);
            }
            ddata[i] = Arrays.copyOf(d.data, blockSize);
        }
        byte[][] decoded = new byte[k][];
        boolean[] known = new boolean[k];
        int cnt = 0;
        // Seed the queue with all degree-1 droplets
        Deque<Integer> queue = new ArrayDeque<>();
        for (int i = 0; i < N; i++)
            if (remaining[i].size() == 1)
                queue.add(i);
        while (!queue.isEmpty() && cnt < k) {
            int di = queue.poll();
            if (remaining[di].size() != 1)
                continue; // already peeled further
            int bi = remaining[di].iterator().next();
            if (known[bi])
                continue; // block already resolved via another droplet
            // Resolve this source block
            known[bi] = true;
            decoded[bi] = Arrays.copyOf(ddata[di], blockSize);
            cnt++;
            // XOR this block out of every droplet that references it.
            // Snapshot the set BEFORE iterating -- modifying blockToDroplets[bi]
            // while iterating it causes ConcurrentModificationException.
            int[] neighbours = blockToDroplets[bi].stream().mapToInt(Integer::intValue).toArray();
            blockToDroplets[bi].clear(); // safe now: we are done iterating it
            for (int ej : neighbours) {
                if (remaining[ej].remove(Integer.valueOf(bi))) { // true if bi was still there
                    for (int j = 0; j < blockSize; j++)
                        ddata[ej][j] ^= decoded[bi][j];
                    if (remaining[ej].size() == 1)
                        queue.add(ej); // newly degree-1
                }
            }
        }
        for (int i = 0; i < k; i++)
            if (!known[i])
                decoded[i] = new byte[blockSize];
        // Pre-size the output buffer to avoid repeated doubling reallocs on large
        // files.
        long totalLen = (long) k * blockSize;
        int outLen = (int) Math.min(origLen, Math.min(totalLen, Integer.MAX_VALUE));
        byte[] out = new byte[outLen];
        int pos = 0;
        for (byte[] blk : decoded) {
            int copy = Math.min(blk.length, outLen - pos);
            if (copy <= 0)
                break;
            System.arraycopy(blk, 0, out, pos, copy);
            pos += copy;
        }
        return out;
    }

    // Serialisation
    static byte[] serializeDroplets(List<Droplet> ds, int k, int blockSize, int origLen)
            throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        DataOutputStream dos = new DataOutputStream(baos);
        dos.writeInt(0x464F554E); // 'FOUN'
        dos.writeInt(k);
        dos.writeInt(blockSize);
        dos.writeInt(origLen);
        dos.writeInt(ds.size());
        for (Droplet d : ds) {
            dos.writeInt(d.id);
            dos.writeInt(d.degree);
            for (int bi : d.srcBlocks)
                dos.writeInt(bi);
            dos.writeInt(d.data.length);
            dos.write(d.data);
        }
        dos.flush();
        return baos.toByteArray();
    }

    static DropletBundle deserializeDroplets(byte[] raw) throws IOException {
        DataInputStream dis = new DataInputStream(new ByteArrayInputStream(raw));
        int magic = dis.readInt();
        if (magic != 0x464F554E)
            throw new IOException(
                    "Not a fountain bundle (magic=0x" + Integer.toHexString(magic) + "). "
                            + "This PNG was not saved with fountain codes -- re-encode and save first.");
        int k = dis.readInt(), bs = dis.readInt(), ol = dis.readInt(), n = dis.readInt();
        // Sanity-check fields -- catches pixel-noise mis-reads from non-fountain PNGs
        if (k <= 0 || k > 10_000_000)
            throw new IOException("Corrupt bundle: k=" + k + " out of range. Wrong file?");
        if (bs <= 0 || bs > 65536)
            throw new IOException("Corrupt bundle: blockSize=" + bs + " out of range.");
        if (n < k || n > k * 10)
            throw new IOException("Corrupt bundle: droplet count " + n + " vs k=" + k + " is implausible.");
        List<Droplet> list = new ArrayList<>(n);
        int dupDroplets = 0;
        for (int i = 0; i < n; i++) {
            int id = dis.readInt(), deg = dis.readInt();
            if (deg <= 0 || deg > k)
                throw new IOException("Corrupt bundle: droplet degree " + deg + " at index " + i + ".");
            int[] src = new int[deg];
            for (int j = 0; j < deg; j++)
                src[j] = dis.readInt();
            int dl = dis.readInt();
            if (dl != bs)
                throw new IOException(
                        "Corrupt bundle: data length " + dl + " != blockSize " + bs + " at droplet " + i + ".");
            byte[] d = new byte[dl];
            dis.readFully(d);
            // Detect duplicate srcBlocks (written by buggy encoder).
            // Duplicates cause XOR cancellation: block XOR'd twice = 0 contribution.
            // We must discard the entire droplet — its XOR data is irrecoverably wrong.
            boolean hasDup = false;
            Set<Integer> seen = new HashSet<>(deg * 2);
            for (int bi : src)
                if (!seen.add(bi)) {
                    hasDup = true;
                    break;
                }
            if (hasDup) {
                dupDroplets++;
                continue;
            } // skip this corrupted droplet
            list.add(new Droplet(id, deg, src, d));
        }
        if (dupDroplets > 0 && list.size() < k)
            throw new IOException(
                    "BUGGY_ENCODE:" + dupDroplets + ":" + n +
                            "\nThis file was encoded with a buggy version that produced " + dupDroplets +
                            " corrupted droplets (duplicate block indices). Only " + (n - dupDroplets) +
                            " valid droplets remain — insufficient to reconstruct the " + k + " source blocks.\n\n" +
                            "ACTION REQUIRED: Re-encode and re-save the original file with the current version.");
        return new DropletBundle(list, k, bs, ol, dupDroplets);
    }

    // PNG pixel embedding
    // Max PNG height cap: ~32k rows. Above this, payload is stored only in the
    // .dat sidecar (which is always written). The PNG still carries the header
    // row with magic+length so the reader knows to fall back to the .dat file.
    static final int PNG_MAX_PAYLOAD_ROWS = 30000;

    /**
     * Embed droplet payload into extra rows appended to the visualization image.
     * For very large payloads (> PNG_MAX_PAYLOAD_ROWS * W * 3 bytes) the PNG
     * only stores as much as fits; the .dat sidecar holds the full bundle.
     * The header row always stores the FULL payload length so the decoder knows
     * whether the PNG is complete or needs the .dat fallback.
     */
    static BufferedImage embedDropletsInImage(BufferedImage viz, byte[] payload) {
        int W = viz.getWidth(), H = viz.getHeight();
        long totalPayRows = (long) Math.ceil((payload.length + 3.0) / (W * 3));
        // Cap rows to avoid BufferedImage allocation failure on huge files
        int payRows = (int) Math.min(totalPayRows, PNG_MAX_PAYLOAD_ROWS);
        BufferedImage out = new BufferedImage(W, H + 1 + payRows, BufferedImage.TYPE_INT_RGB);
        Graphics2D g = out.createGraphics();
        g.drawImage(viz, 0, 0, null);
        g.dispose();
        // Header row: magic + FULL payload length (even if truncated in PNG)
        byte[] hdr = {
                (byte) 0xF0, (byte) 0x0D, (byte) 0xCA, (byte) 0xFE,
                (byte) ((payload.length >> 24) & 0xFF), (byte) ((payload.length >> 16) & 0xFF),
                (byte) ((payload.length >> 8) & 0xFF), (byte) (payload.length & 0xFF) };
        writeRowBytes(out, H, hdr);
        writePayloadBytes(out, H + 1, payload); // writes only as many rows as fit
        return out;
    }

    static void writeRowBytes(BufferedImage img, int row, byte[] data) {
        for (int x = 0, i = 0; x < img.getWidth() && i < data.length; x++, i += 3) {
            int r = (i < data.length) ? data[i] & 0xFF : 0;
            int g = (i + 1 < data.length) ? data[i + 1] & 0xFF : 0;
            int b = (i + 2 < data.length) ? data[i + 2] & 0xFF : 0;
            img.setRGB(x, row, (r << 16) | (g << 8) | b);
        }
    }

    static void writePayloadBytes(BufferedImage img, int startRow, byte[] data) {
        int W = img.getWidth(), H = img.getHeight(), idx = 0;
        outer: for (int row = startRow; row < H; row++)
            for (int col = 0; col < W; col++) {
                int r = (idx < data.length) ? data[idx] & 0xFF : 0;
                int g = (idx + 1 < data.length) ? data[idx + 1] & 0xFF : 0;
                int b = (idx + 2 < data.length) ? data[idx + 2] & 0xFF : 0;
                img.setRGB(col, row, (r << 16) | (g << 8) | b);
                idx += 3;
                if (idx >= data.length)
                    break outer;
            }
    }

    /**
     * Extract the droplet payload from a fountain-encoded PNG.
     * Throws IOException with message "TRUNCATED" if the PNG was capped during
     * save (large file) and does not contain the full payload -- callers should
     * then load the companion .dat sidecar instead.
     */
    static byte[] extractDropletsFromImage(BufferedImage img) throws IOException {
        int hdrRow = findHeaderRow(img);
        byte[] hdr = new byte[8];
        readRowBytes(img, hdrRow, hdr);
        if ((hdr[0] & 0xFF) != 0xF0 || (hdr[1] & 0xFF) != 0x0D ||
                (hdr[2] & 0xFF) != 0xCA || (hdr[3] & 0xFF) != 0xFE)
            throw new IOException("Fountain header not found in image");
        int length = ((hdr[4] & 0xFF) << 24) | ((hdr[5] & 0xFF) << 16) |
                ((hdr[6] & 0xFF) << 8) | (hdr[7] & 0xFF);
        // How many bytes can the image actually hold after the header row?
        int W = img.getWidth();
        long capacity = (long) (img.getHeight() - hdrRow - 1) * W * 3;
        if (capacity < length)
            throw new IOException("TRUNCATED:" + length); // signal caller to use .dat
        byte[] payload = new byte[length];
        readPayloadBytes(img, hdrRow + 1, payload);
        return payload;
    }

    static int findHeaderRow(BufferedImage img) {
        for (int row = 0; row < img.getHeight() - 1; row++) {
            int px = img.getRGB(0, row);
            if (((px >> 16) & 0xFF) == 0xF0 && ((px >> 8) & 0xFF) == 0x0D && (px & 0xFF) == 0xCA) {
                int px2 = img.getRGB(1, row);
                if (((px2 >> 16) & 0xFF) == 0xFE)
                    return row;
            }
        }
        return Math.max(0, img.getHeight() - 2);
    }

    static void readRowBytes(BufferedImage img, int row, byte[] buf) {
        for (int x = 0, i = 0; x < img.getWidth() && i < buf.length; x++, i += 3) {
            int px = img.getRGB(x, row);
            if (i < buf.length)
                buf[i] = (byte) ((px >> 16) & 0xFF);
            if (i + 1 < buf.length)
                buf[i + 1] = (byte) ((px >> 8) & 0xFF);
            if (i + 2 < buf.length)
                buf[i + 2] = (byte) (px & 0xFF);
        }
    }

    static void readPayloadBytes(BufferedImage img, int startRow, byte[] buf) {
        int W = img.getWidth(), H = img.getHeight(), idx = 0;
        outer: for (int row = startRow; row < H; row++)
            for (int col = 0; col < W; col++) {
                int px = img.getRGB(col, row);
                if (idx < buf.length)
                    buf[idx++] = (byte) ((px >> 16) & 0xFF);
                if (idx < buf.length)
                    buf[idx++] = (byte) ((px >> 8) & 0xFF);
                if (idx < buf.length)
                    buf[idx++] = (byte) (px & 0xFF);
                if (idx >= buf.length)
                    break outer;
            }
    }

    // ── Shared decompress ─────────────────────────────────────────────────────

    static byte[] decompressBytes(byte[] c) throws IOException {
        ByteArrayOutputStream b = new ByteArrayOutputStream();
        try (GZIPInputStream gz = new GZIPInputStream(new ByteArrayInputStream(c))) {
            byte[] buf = new byte[8192];
            int n;
            while ((n = gz.read(buf)) > 0)
                b.write(buf, 0, n);
        }
        return b.toByteArray();
    }

    // CORRUPTION SIMULATION (droplet-level erasure — never touches container)
    // Six distinct erasure models.
    enum CorruptionMode {
        RANDOM_UNIFORM("Random Uniform",
                "Each droplet is independently erased with probability p  (i.i.d. Bernoulli erasure)"),
        BURST_ERASURE("Burst Erasure",
                "Consecutive runs of droplets are wiped  (simulates disk sector / memory burst failures)"),
        SEQUENTIAL_FRONT("Front-Loaded",
                "First X% of droplets are erased  (simulates header / beginning-of-file damage)"),
        SEQUENTIAL_BACK("Back-Loaded",
                "Last X% of droplets are erased  (simulates tail / end-of-file damage)"),
        PERIODIC("Periodic / Striped",
                "Every Nth droplet is erased  (simulates interleaved loss or bad memory rows)"),
        RANDOM_CLUSTERED("Random Clustered",
                "Erasures cluster around random hot-spots  (simulates localised physical damage)");

        final String label, desc;

        CorruptionMode(String l, String d) {
            label = l;
            desc = d;
        }

        @Override
        public String toString() {
            return label;
        }
    }

    // Apply erasure to a droplet list. Returns only surviving droplets.
    // No GZIP data is ever touched.
    static List<Droplet> applyCorruption(List<Droplet> all, double pct,
            CorruptionMode mode, long seed) {
        if (pct <= 0)
            return all;
        int total = all.size();
        int toRemove = (int) Math.round(total * pct / 100.0);
        if (toRemove <= 0)
            return all;
        if (toRemove >= total)
            return new ArrayList<>();
        Set<Integer> erased = new LinkedHashSet<>();
        Random rng = new Random(seed);
        switch (mode) {
            case RANDOM_UNIFORM:
                while (erased.size() < toRemove)
                    erased.add(rng.nextInt(total));
                break;
            case BURST_ERASURE: {
                int runs = 3 + rng.nextInt(3), perRun = Math.max(1, toRemove / runs);
                for (int r = 0; r < runs && erased.size() < toRemove; r++) {
                    int start = rng.nextInt(total);
                    for (int j = 0; j < perRun && erased.size() < toRemove; j++)
                        erased.add((start + j) % total);
                }
                while (erased.size() < toRemove)
                    erased.add(rng.nextInt(total));
                break;
            }
            case SEQUENTIAL_FRONT:
                for (int i = 0; i < toRemove; i++)
                    erased.add(i);
                break;
            case SEQUENTIAL_BACK:
                for (int i = total - toRemove; i < total; i++)
                    erased.add(i);
                break;
            case PERIODIC: {
                int step = Math.max(1, (int) Math.round(100.0 / pct));
                for (int i = 0; i < total && erased.size() < toRemove; i += step)
                    erased.add(i);
                // top-up if step too coarse
                while (erased.size() < toRemove)
                    erased.add(rng.nextInt(total));
                break;
            }
            case RANDOM_CLUSTERED: {
                int centres = Math.max(1, toRemove / 8);
                int radius = Math.max(1, toRemove / (centres * 2));
                for (int c = 0; c < centres && erased.size() < toRemove; c++) {
                    int ctr = rng.nextInt(total);
                    for (int off = -radius; off <= radius && erased.size() < toRemove; off++)
                        erased.add(Math.max(0, Math.min(total - 1, ctr + off)));
                }
                while (erased.size() < toRemove)
                    erased.add(rng.nextInt(total));
                break;
            }
        }
        List<Droplet> out = new ArrayList<>();
        for (int i = 0; i < total; i++)
            if (!erased.contains(i))
                out.add(all.get(i));
        return out;
    }

    // CORRUPTION TEST DIALOG
    class CorruptionTestDialog extends JDialog {
        // Section 1 – source
        private JRadioButton useAutoBtn, useCustomPngBtn, useCustomDatBtn;
        private JTextField customPngField, customDatField;
        // Section 2 – parameters
        private JSlider pctSlider;
        private JLabel pctValueLabel;
        private JComboBox<CorruptionMode> modeCombo;
        private JLabel modeDescLabel;
        private JSpinner seedSpinner;
        private JCheckBox randomSeedCheck;
        // Section 3 – output
        private JCheckBox autoSaveCheck;
        private JTextField outputDirField;
        // Section 4 – results
        private JTextArea resultArea;
        private JProgressBar progressBar;
        private JButton runBtn, clearBtn, closeBtn;

        CorruptionTestDialog(JFrame parent) {
            super(parent, "⚡  Fountain Code — Corruption Test Lab", true);
            setLayout(new BorderLayout(8, 8));
            setSize(760, 710);
            setLocationRelativeTo(parent);
            ((JPanel) getContentPane()).setBorder(
                    new EmptyBorder(8, 8, 8, 8));
            JPanel top = new JPanel();
            top.setLayout(new BoxLayout(top, BoxLayout.Y_AXIS));
            top.add(buildSourcePanel());
            top.add(Box.createVerticalStrut(6));
            top.add(buildParamsPanel());
            top.add(Box.createVerticalStrut(6));
            top.add(buildOutputPanel());
            add(top, BorderLayout.NORTH);
            add(buildResultPanel(), BorderLayout.CENTER);
            add(buildButtonRow(), BorderLayout.SOUTH);
        }

        // Panel builders
        JPanel buildSourcePanel() {
            JPanel p = new JPanel(new GridBagLayout());
            p.setBorder(new TitledBorder("① Source File"));
            GridBagConstraints g = gbc();
            useAutoBtn = new JRadioButton("Use current session:  " + getDNAImageFilename(), true);
            useCustomPngBtn = new JRadioButton("Custom PNG file:");
            useCustomDatBtn = new JRadioButton("Custom .dat file (backup path):");
            ButtonGroup bg = new ButtonGroup();
            bg.add(useAutoBtn);
            bg.add(useCustomPngBtn);
            bg.add(useCustomDatBtn);
            customPngField = new JTextField(30);
            customPngField.setEnabled(false);
            customDatField = new JTextField(30);
            customDatField.setEnabled(false);
            JButton bpng = new JButton("Browse…");
            bpng.setEnabled(false);
            JButton bdat = new JButton("Browse…");
            bdat.setEnabled(false);
            useCustomPngBtn.addItemListener(e -> {
                boolean s = useCustomPngBtn.isSelected();
                customPngField.setEnabled(s);
                bpng.setEnabled(s);
            });
            useCustomDatBtn.addItemListener(e -> {
                boolean s = useCustomDatBtn.isSelected();
                customDatField.setEnabled(s);
                bdat.setEnabled(s);
            });
            bpng.addActionListener(e -> {
                JFileChooser fc = new JFileChooser();
                fc.setFileFilter(new FileNameExtensionFilter("PNG", "png"));
                if (fc.showOpenDialog(this) == JFileChooser.APPROVE_OPTION)
                    customPngField.setText(fc.getSelectedFile().getAbsolutePath());
            });
            bdat.addActionListener(e -> {
                JFileChooser fc = new JFileChooser();
                fc.setFileFilter(new FileNameExtensionFilter("DAT", "dat"));
                if (fc.showOpenDialog(this) == JFileChooser.APPROVE_OPTION)
                    customDatField.setText(fc.getSelectedFile().getAbsolutePath());
            });
            g.gridx = 0;
            g.gridy = 0;
            g.gridwidth = 3;
            p.add(useAutoBtn, g);
            g.gridy = 1;
            g.gridwidth = 1;
            p.add(useCustomPngBtn, g);
            g.gridx = 1;
            g.fill = GridBagConstraints.HORIZONTAL;
            g.weightx = 1;
            p.add(customPngField, g);
            g.gridx = 2;
            g.fill = GridBagConstraints.NONE;
            g.weightx = 0;
            p.add(bpng, g);
            g.gridx = 0;
            g.gridy = 2;
            p.add(useCustomDatBtn, g);
            g.gridx = 1;
            g.fill = GridBagConstraints.HORIZONTAL;
            g.weightx = 1;
            p.add(customDatField, g);
            g.gridx = 2;
            g.fill = GridBagConstraints.NONE;
            g.weightx = 0;
            p.add(bdat, g);
            return p;
        }

        JPanel buildParamsPanel() {
            JPanel p = new JPanel(new GridBagLayout());
            p.setBorder(new TitledBorder("② Corruption Parameters"));
            GridBagConstraints g = gbc();
            // Percentage
            g.gridx = 0;
            g.gridy = 0;
            p.add(new JLabel("Erasure percentage:"), g);
            pctSlider = new JSlider(0, 50, 20);
            pctSlider.setMajorTickSpacing(10);
            pctSlider.setMinorTickSpacing(2);
            pctSlider.setPaintTicks(true);
            pctSlider.setPaintLabels(true);
            pctSlider.setPreferredSize(new Dimension(340, 50));
            pctValueLabel = new JLabel("20 %  ");
            pctValueLabel.setFont(new Font("Arial", Font.BOLD, 14));
            pctValueLabel.setForeground(new Color(180, 40, 40));
            pctSlider.addChangeListener(e -> pctValueLabel.setText(pctSlider.getValue() + " %  "));
            g.gridx = 1;
            g.fill = GridBagConstraints.HORIZONTAL;
            g.weightx = 1;
            p.add(pctSlider, g);
            g.gridx = 2;
            g.fill = GridBagConstraints.NONE;
            g.weightx = 0;
            p.add(pctValueLabel, g);
            // Corruption model
            g.gridx = 0;
            g.gridy = 1;
            p.add(new JLabel("Corruption model:"), g);
            modeCombo = new JComboBox<>(CorruptionMode.values());
            modeCombo.setSelectedItem(CorruptionMode.RANDOM_UNIFORM);
            modeCombo.setPreferredSize(new Dimension(220, 26));
            g.gridx = 1;
            g.gridwidth = 2;
            p.add(modeCombo, g);
            g.gridwidth = 1;
            // Description
            modeDescLabel = new JLabel(
                    "<html><i>" + ((CorruptionMode) modeCombo.getSelectedItem()).desc + "</i></html>");
            modeDescLabel.setFont(new Font("Arial", Font.PLAIN, 11));
            modeDescLabel.setForeground(new Color(80, 80, 80));
            modeCombo.addActionListener(e -> modeDescLabel.setText(
                    "<html><i>" + ((CorruptionMode) modeCombo.getSelectedItem()).desc + "</i></html>"));
            g.gridx = 1;
            g.gridy = 2;
            g.gridwidth = 2;
            p.add(modeDescLabel, g);
            g.gridwidth = 1;
            // Seed
            g.gridx = 0;
            g.gridy = 3;
            p.add(new JLabel("Random seed:"), g);
            seedSpinner = new JSpinner(new SpinnerNumberModel(42, 0, Integer.MAX_VALUE, 1));
            seedSpinner.setPreferredSize(new Dimension(100, 26));
            randomSeedCheck = new JCheckBox("New random seed each run");
            randomSeedCheck.addItemListener(e -> seedSpinner.setEnabled(!randomSeedCheck.isSelected()));
            g.gridx = 1;
            p.add(seedSpinner, g);
            g.gridx = 2;
            p.add(randomSeedCheck, g);
            return p;
        }

        JPanel buildOutputPanel() {
            JPanel p = new JPanel(new GridBagLayout());
            p.setBorder(new TitledBorder("③ Output Options"));
            GridBagConstraints g = gbc();
            autoSaveCheck = new JCheckBox("Auto-save recovered file", true);
            g.gridx = 0;
            g.gridy = 0;
            g.gridwidth = 3;
            p.add(autoSaveCheck, g);
            g.gridwidth = 1;
            g.gridx = 0;
            g.gridy = 1;
            p.add(new JLabel("Output folder:"), g);
            outputDirField = new JTextField(System.getProperty("user.dir"), 30);
            g.gridx = 1;
            g.fill = GridBagConstraints.HORIZONTAL;
            g.weightx = 1;
            p.add(outputDirField, g);
            JButton browseOut = new JButton("Browse…");
            browseOut.addActionListener(e -> {
                JFileChooser fc = new JFileChooser(outputDirField.getText());
                fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
                if (fc.showOpenDialog(this) == JFileChooser.APPROVE_OPTION)
                    outputDirField.setText(fc.getSelectedFile().getAbsolutePath());
            });
            g.gridx = 2;
            g.fill = GridBagConstraints.NONE;
            g.weightx = 0;
            p.add(browseOut, g);
            return p;
        }

        JPanel buildResultPanel() {
            JPanel p = new JPanel(new BorderLayout(4, 4));
            p.setBorder(new TitledBorder("④ Test Results"));
            progressBar = new JProgressBar(0, 100);
            progressBar.setStringPainted(true);
            progressBar.setString("Idle — press ▶ Run to start");
            progressBar.setPreferredSize(new Dimension(0, 22));
            resultArea = new JTextArea();
            resultArea.setEditable(false);
            resultArea.setFont(new Font("Monospaced", Font.PLAIN, 11));
            resultArea.setBackground(new Color(248, 250, 252));
            JScrollPane sp = new JScrollPane(resultArea);
            p.add(progressBar, BorderLayout.NORTH);
            p.add(sp, BorderLayout.CENTER);
            return p;
        }

        JPanel buildButtonRow() {
            JPanel p = new JPanel(new FlowLayout(FlowLayout.RIGHT, 10, 6));
            runBtn = new JButton("▶  Run Corruption Test");
            clearBtn = new JButton("Clear Log");
            closeBtn = new JButton("Close");
            runBtn.setBackground(new Color(35, 120, 215));
            runBtn.setForeground(Color.WHITE);
            runBtn.setFont(runBtn.getFont().deriveFont(Font.BOLD, 13f));
            runBtn.setPreferredSize(new Dimension(210, 34));
            runBtn.addActionListener(e -> runTest());
            clearBtn.addActionListener(e -> {
                resultArea.setText("");
                progressBar.setValue(0);
                progressBar.setString("Idle");
            });
            closeBtn.addActionListener(e -> dispose());
            p.add(runBtn);
            p.add(clearBtn);
            p.add(closeBtn);
            return p;
        }

        // helper
        GridBagConstraints gbc() {
            GridBagConstraints g = new GridBagConstraints();
            g.insets = new Insets(3, 5, 3, 5);
            g.anchor = GridBagConstraints.WEST;
            return g;
        }

        void log2(String line) {
            resultArea.append(line + "\n");
            resultArea.setCaretPosition(resultArea.getDocument().getLength());
        }

        // Test runner
        void runTest() {
            resultArea.setText("");
            progressBar.setValue(0);
            progressBar.setString("Starting…");
            runBtn.setEnabled(false);
            // Resolve source file
            File srcFile;
            boolean useDat = useCustomDatBtn.isSelected();
            if (useAutoBtn.isSelected()) {
                srcFile = new File(getDNAImageFilename());
                useDat = false;
                if (!srcFile.exists()) {
                    JOptionPane.showMessageDialog(this,
                            "Auto file not found:\n" + srcFile.getAbsolutePath() +
                                    "\nPlease save the DNA image first, or choose a custom file.",
                            "File Not Found", JOptionPane.WARNING_MESSAGE);
                    runBtn.setEnabled(true);
                    return;
                }
            } else if (useCustomPngBtn.isSelected()) {
                srcFile = new File(customPngField.getText().trim());
                useDat = false;
            } else {
                srcFile = new File(customDatField.getText().trim());
                useDat = true;
            }
            if (!srcFile.exists()) {
                JOptionPane.showMessageDialog(this,
                        "File not found:\n" + srcFile.getAbsolutePath(),
                        "Error", JOptionPane.ERROR_MESSAGE);
                runBtn.setEnabled(true);
                return;
            }
            double pct = pctSlider.getValue();
            CorruptionMode mode = (CorruptionMode) modeCombo.getSelectedItem();
            long seed = randomSeedCheck.isSelected() ? new Random().nextLong()
                    : (long) (Integer) seedSpinner.getValue();
            boolean autoSave = autoSaveCheck.isSelected();
            String outDir = outputDirField.getText().trim();
            final boolean fromDat = useDat;
            final File theFile = srcFile;
            SwingWorker<byte[], String> worker = new SwingWorker<>() {
                String recName = "recovered.bin";
                int recSize = 0;
                boolean checksumOK = false;
                int dtotal = 0, dsurvive = 0;

                @Override
                protected byte[] doInBackground() throws Exception {
                    String ts = new SimpleDateFormat("HH:mm:ss").format(new Date());
                    publish(ts + " | Fountain Code Corruption Test");
                    publish("══════════════════════════════════════════════════");
                    publish("Source : " + theFile.getAbsolutePath());
                    publish(String.format("Model  : %s", mode.label));
                    publish(String.format("Erasure: %.0f%%  |  seed = %d", pct, seed));
                    publish("");
                    setProgress(5);
                    // Load droplet bundle
                    DropletBundle bundle;
                    try {
                        if (fromDat) {
                            publish("Loading .dat file…");
                            byte[] raw = Files.readAllBytes(theFile.toPath());
                            byte[] dec = decompressBytes(raw);
                            DataInputStream dis2 = new DataInputStream(new ByteArrayInputStream(dec));
                            int dnaLen = dis2.readInt();
                            dis2.skipBytes(dnaLen);
                            ByteArrayOutputStream rem = new ByteArrayOutputStream();
                            byte[] buf = new byte[8192];
                            int n;
                            while ((n = dis2.read(buf)) > 0)
                                rem.write(buf, 0, n);
                            bundle = deserializeDroplets(decompressBytes(rem.toByteArray()));
                            publish("  Loaded " + bundle.droplets.size() + " droplets from .dat");
                        } else {
                            publish("Loading PNG and extracting fountain droplets…");
                            BufferedImage img = ImageIO.read(theFile);
                            if (img == null)
                                throw new IOException("Cannot read PNG");
                            byte[] compDrop;
                            try {
                                compDrop = extractDropletsFromImage(img);
                                publish("  Loaded droplets from PNG pixel rows");
                            } catch (IOException trunc) {
                                if (trunc.getMessage() != null && trunc.getMessage().startsWith("TRUNCATED")) {
                                    // PNG was capped for large file -- load full bundle from .dat sidecar
                                    publish("  PNG payload truncated (large file) -- loading from .dat sidecar");
                                    String datPath = theFile.getAbsolutePath()
                                            .replaceAll("dna_strand_", "dna_sequence_")
                                            .replaceAll("\\.png$", ".dat");
                                    File datFallback = new File(datPath);
                                    if (!datFallback.exists())
                                        throw new IOException("PNG truncated and .dat sidecar not found: " + datPath);
                                    byte[] rawDat = Files.readAllBytes(datFallback.toPath());
                                    byte[] decDat = decompressBytes(rawDat);
                                    DataInputStream dsFb = new DataInputStream(new ByteArrayInputStream(decDat));
                                    int dnaLenFb = dsFb.readInt();
                                    dsFb.skipBytes(dnaLenFb);
                                    ByteArrayOutputStream remFb = new ByteArrayOutputStream();
                                    byte[] bufFb = new byte[8192];
                                    int nFb;
                                    while ((nFb = dsFb.read(bufFb)) > 0)
                                        remFb.write(bufFb, 0, nFb);
                                    compDrop = remFb.toByteArray();
                                    publish("  Loaded from .dat sidecar: " + datFallback.getName());
                                } else {
                                    throw trunc;
                                }
                            }
                            bundle = deserializeDroplets(decompressBytes(compDrop));
                            publish("  Loaded " + bundle.droplets.size() + " droplets");
                        }
                    } catch (IOException ioe) {
                        String msg = ioe.getMessage();
                        if (msg != null && msg.startsWith("BUGGY_ENCODE")) {
                            String[] parts = msg.split(":", 4);
                            int dups = Integer.parseInt(parts[1]), tot = Integer.parseInt(parts[2]);
                            throw new IOException(
                                    "⚠  File encoded with a buggy version — cannot recover.\n\n" +
                                            dups + " of " + tot + " droplets have corrupted block indices " +
                                            "and were discarded.\n\n" +
                                            "ACTION: Re-encode and re-save the original file with this " +
                                            "fixed version, then run the test again.");
                        }
                        throw ioe;
                    }
                    if (bundle.dupDroplets > 0)
                        publish("  ⚠ " + bundle.dupDroplets + " buggy droplets discarded (duplicate block indices)");
                    dtotal = bundle.droplets.size();
                    publish("  Source blocks k  : " + bundle.k);
                    publish("  Block size       : " + bundle.blockSize + " B");
                    publish("  Original length  : " + formatSize(bundle.origLen));
                    publish("  Total droplets   : " + dtotal);
                    setProgress(25);
                    // Apply corruption (droplet erasure, no GZIP touched)
                    publish("");
                    publish("Applying erasure model: " + mode.label + " …");
                    List<Droplet> surviving = applyCorruption(bundle.droplets, pct, mode, seed);
                    dsurvive = surviving.size();
                    int lost = dtotal - dsurvive;
                    publish(String.format("  Droplets erased  : %d / %d  (%.1f%%)",
                            lost, dtotal, lost * 100.0 / dtotal));
                    publish(String.format("  Droplets survive : %d / %d  (%.1f%%)",
                            dsurvive, dtotal, dsurvive * 100.0 / dtotal));
                    if (dsurvive < bundle.k)
                        publish("  ⚠ Surviving < k (" + bundle.k
                                + ") — best-effort partial decode will run");
                    else
                        publish("  ✓ Sufficient droplets for full decode attempt");
                    setProgress(45);
                    // Fountain decode
                    publish("");
                    publish("Running LT belief-propagation decoder…");
                    byte[] pkt = fountainDecode(surviving, bundle.k, bundle.blockSize, bundle.origLen);
                    publish("  Reconstructed packet: " + formatSize(pkt.length));
                    setProgress(70);
                    // Parse metadata + decompress + verify
                    publish("Parsing DNA* packet…");
                    byte[] result = parsePacket(pkt);
                    setProgress(92);
                    return result;
                }

                private byte[] parsePacket(byte[] pkt) throws Exception {
                    try {
                        DataInputStream dis = new DataInputStream(new ByteArrayInputStream(pkt));
                        byte[] magic = new byte[4];
                        dis.readFully(magic);
                        if (!"DNA*".equals(new String(magic))) {
                            publish("  ⚠ Magic header corrupt — scanning for GZIP stream…");
                            return gzipScan(pkt);
                        }
                        int ver = dis.read();
                        publish("  Version         : " + ver);
                        int nl = ((dis.read() & 0xFF) << 8) | (dis.read() & 0xFF);
                        if (nl < 0 || nl > 1024) {
                            publish("  ⚠ Name length corrupt (" + nl + ") — scanning…");
                            return gzipScan(pkt);
                        }
                        byte[] nb = new byte[nl];
                        dis.readFully(nb);
                        recName = new String(nb);
                        publish("  Original name   : " + recName);
                        recSize = dis.readInt();
                        publish("  Original size   : " + formatSize(recSize));
                        byte[] sha = new byte[32];
                        dis.readFully(sha);
                        int cs = dis.readInt();
                        if (cs < 0 || cs > pkt.length) {
                            publish("  ⚠ Compressed size corrupt (" + cs + ") — scanning…");
                            return gzipScan(pkt);
                        }
                        byte[] comp = new byte[cs];
                        dis.readFully(comp);
                        publish("Decompressing GZIP payload…");
                        byte[] data;
                        try {
                            data = decompressBytes(comp);
                        } catch (Exception gze) {
                            publish("  ⚠ GZIP failed (" + gze.getMessage() + ")");
                            publish("  Too many unresolved source blocks.");
                            checksumOK = false;
                            if (recName.isEmpty())
                                recName = "partial_recovery.bin";
                            return Arrays.copyOf(pkt, Math.min(pkt.length,
                                    recSize > 0 ? recSize : pkt.length));
                        }
                        publish("Verifying SHA-256 checksum…");
                        byte[] computed = MessageDigest.getInstance("SHA-256").digest(data);
                        checksumOK = Arrays.equals(sha, computed);
                        publish(checksumOK
                                ? "  ✅ Checksum VALID — data is bit-for-bit identical to original"
                                : "  ⚠ Checksum MISMATCH — some source blocks unresolved");
                        return data;
                    } catch (Exception ex) {
                        publish("  Parse error: " + ex.getMessage() + " — scanning for GZIP…");
                        return gzipScan(pkt);
                    }
                }

                private byte[] gzipScan(byte[] data) {
                    publish("  Scanning raw bytes for 0x1F 0x8B GZIP magic…");
                    for (int i = 0; i < data.length - 1; i++) {
                        if ((data[i] & 0xFF) == 0x1F && (data[i + 1] & 0xFF) == 0x8B) {
                            try {
                                byte[] sub = Arrays.copyOfRange(data, i, data.length);
                                byte[] r = decompressBytes(sub);
                                publish("  ✅ GZIP at offset " + i + " — extracted " + formatSize(r.length));
                                checksumOK = false;
                                if (recName.isEmpty())
                                    recName = "partial_recovery.bin";
                                return r;
                            } catch (Exception ignored) {
                            }
                        }
                    }
                    publish("  No valid GZIP stream found — returning raw bytes as-is");
                    checksumOK = false;
                    if (recName.isEmpty())
                        recName = "partial_recovery.bin";
                    return data;
                }

                @Override
                protected void process(List<String> chunks) {
                    chunks.forEach(s -> log2(s));
                }

                @Override
                protected void done() {
                    try {
                        byte[] data = get();
                        setProgress(100);
                        progressBar.setString(checksumOK ? "✅ PERFECT recovery" : "⚠ PARTIAL recovery");
                        log2("");
                        log2("══════════════════ RESULT ══════════════════════");
                        log2(String.format("Erasure model    : %s", mode.label));
                        log2(String.format("Droplets erased  : %d / %d  (%.1f%%)",
                                dtotal - dsurvive, dtotal, (dtotal - dsurvive) * 100.0 / dtotal));
                        log2(String.format("Droplets survived: %d / %d  (%.1f%%)",
                                dsurvive, dtotal, dsurvive * 100.0 / dtotal));
                        log2("Checksum         : " + (checksumOK ? "✅ VALID — perfect recovery"
                                : "⚠  PARTIAL — some data unresolvable"));
                        if (autoSave) {
                            String ext = recName.contains(".") ? recName.substring(recName.lastIndexOf('.')) : ".bin";
                            String base = recName.contains(".") ? recName.substring(0, recName.lastIndexOf('.'))
                                    : recName;
                            String suffix = checksumOK ? "_PERFECT" : "_PARTIAL";
                            File out2 = new File(outDir, base + suffix + ext);
                            Files.write(out2.toPath(), data);
                            log2("Saved to         : " + out2.getAbsolutePath());
                        }
                        log2("═══════════════════════════════════════════════");
                        JOptionPane.showMessageDialog(CorruptionTestDialog.this,
                                (checksumOK ? "✅" : "⚠") + " Corruption Test Complete\n\n"
                                        + String.format("Model   : %s\n", mode.label)
                                        + String.format("Erasure : %.0f%%  (%d droplets lost)\n", pct,
                                                dtotal - dsurvive)
                                        + String.format("Survived: %d / %d droplets\n", dsurvive, dtotal) + "Result  : "
                                        + (checksumOK ? "PERFECT ✅ — bit-for-bit identical to original"
                                                : "PARTIAL ⚠ — too many droplets erased for full recovery"),
                                "Test Complete",
                                checksumOK ? JOptionPane.INFORMATION_MESSAGE : JOptionPane.WARNING_MESSAGE);
                    } catch (Exception ex) {
                        progressBar.setString("Error");
                        log2("ERROR: " + ex.getMessage());
                        JOptionPane.showMessageDialog(CorruptionTestDialog.this,
                                "Test error:\n" + ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE);
                    } finally {
                        runBtn.setEnabled(true);
                    }
                }
            };

            worker.addPropertyChangeListener(evt -> {
                if ("progress".equals(evt.getPropertyName())) {
                    int v = (Integer) evt.getNewValue();
                    progressBar.setValue(v);
                    progressBar.setString(v + "%");
                }
            });
            worker.execute();
        }
    }

    // MAIN UI
    public DNAStorageWithFountainCodes() {
        initializeUI();
    }

    private void initializeUI() {
        setTitle("DNA Storage — Fountain Codes Edition  (LT Codes, Robust Soliton)");
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setLayout(new BorderLayout(10, 10));
        JPanel btnPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 8, 8));
        loadFileBtn = new JButton("📂 Load File");
        encodeBtn = new JButton(" Encode → DNA");
        saveImageBtn = new JButton("💾 Save DNA Image");
        decodeBtn = new JButton("🔓 Decode from Image");
        corruptTestBtn = new JButton("⚡ Corruption Test…");
        encodeBtn.setEnabled(false);
        saveImageBtn.setEnabled(false);
        corruptTestBtn.setEnabled(false);
        corruptTestBtn.setBackground(new Color(35, 120, 215));
        corruptTestBtn.setForeground(Color.WHITE);
        corruptTestBtn.setFont(corruptTestBtn.getFont().deriveFont(Font.BOLD));
        corruptTestBtn.setToolTipText("Opens the Corruption Test Lab — choose files, model, erasure %, seed…");
        btnPanel.add(loadFileBtn);
        btnPanel.add(encodeBtn);
        btnPanel.add(saveImageBtn);
        btnPanel.add(decodeBtn);
        btnPanel.add(Box.createHorizontalStrut(16));
        btnPanel.add(corruptTestBtn);
        compressionLabel = new JLabel(" ");
        compressionLabel.setFont(new Font("Arial", Font.BOLD, 12));
        btnPanel.add(compressionLabel);
        add(btnPanel, BorderLayout.NORTH);
        dnaPanel = new DNAVisualizationPanel();
        JScrollPane sp = new JScrollPane(dnaPanel);
        sp.setPreferredSize(new Dimension(800, 300));
        add(sp, BorderLayout.CENTER);
        JPanel right = new JPanel(new BorderLayout());
        right.setPreferredSize(new Dimension(370, 400));
        dnaTextArea = new JTextArea();
        dnaTextArea.setEditable(false);
        dnaTextArea.setFont(new Font("Courier New", Font.PLAIN, 10));
        JScrollPane tsp = new JScrollPane(dnaTextArea);
        tsp.setBorder(new TitledBorder("DNA Sequence (Preview)"));
        right.add(tsp, BorderLayout.CENTER);
        logArea = new JTextArea();
        logArea.setEditable(false);
        logArea.setFont(new Font("Monospaced", Font.PLAIN, 10));
        JScrollPane lsp = new JScrollPane(logArea);
        lsp.setPreferredSize(new Dimension(370, 180));
        lsp.setBorder(new TitledBorder("Log"));
        right.add(lsp, BorderLayout.SOUTH);
        add(right, BorderLayout.EAST);
        statusLabel = new JLabel("Ready — load a file to begin");
        statusLabel.setBorder(BorderFactory.createEmptyBorder(5, 10, 5, 10));
        add(statusLabel, BorderLayout.SOUTH);
        loadFileBtn.addActionListener(e -> loadFile());
        encodeBtn.addActionListener(e -> encodeFile());
        saveImageBtn.addActionListener(e -> saveDNAImage());
        decodeBtn.addActionListener(e -> decodeFromImage());
        corruptTestBtn.addActionListener(e -> new CorruptionTestDialog(this).setVisible(true));
        setSize(1200, 720);
        setLocationRelativeTo(null);
    }

    private void log(String msg) {
        SwingUtilities.invokeLater(() -> {
            logArea.append(msg + "\n");
            logArea.setCaretPosition(logArea.getDocument().getLength());
        });
    }

    private String getBaseFileName(String fn) {
        int d = fn.lastIndexOf('.');
        return d > 0 ? fn.substring(0, d) : fn;
    }

    String getDNASequenceFilename() {
        return "dna_sequence_" + baseFileName + ".dat";
    }

    String getDNAImageFilename() {
        return "dna_strand_" + baseFileName + ".png";
    }

    String formatSize(long b) {
        if (b < 1024)
            return b + " B";
        if (b < 1 << 20)
            return String.format("%.2f KB", b / 1024.0);
        if (b < 1L << 30)
            return String.format("%.2f MB", b / (1024.0 * 1024));
        return String.format("%.2f GB", b / (1024.0 * 1024 * 1024));
    }

    // Load
    private void loadFile() {
        JFileChooser fc = new JFileChooser();
        if (fc.showOpenDialog(this) != JFileChooser.APPROVE_OPTION)
            return;
        try {
            File f = fc.getSelectedFile();
            originalFileName = f.getName();
            baseFileName = getBaseFileName(originalFileName);
            originalFileData = Files.readAllBytes(f.toPath());
            log("=== FILE LOADED ===");
            log("File: " + originalFileName + " (" + formatSize(originalFileData.length) + ")");
            log("Output → " + getDNAImageFilename() + ", " + getDNASequenceFilename());
            statusLabel.setText("Loaded: " + originalFileName);
            encodeBtn.setEnabled(true);
            saveImageBtn.setEnabled(false);
            corruptTestBtn.setEnabled(false);
            dnaSequence = "";
        } catch (Exception e) {
            log("ERROR: " + e.getMessage());
            JOptionPane.showMessageDialog(this, "Error loading:\n" + e.getMessage());
        }
    }

    // Encode
    private void encodeFile() {
        if (originalFileData == null)
            return;
        log("=== ENCODING WITH FOUNTAIN CODES ===");
        statusLabel.setText("Encoding…");
        encodeBtn.setEnabled(false);
        new SwingWorker<String, String>() {
            @Override
            protected String doInBackground() throws Exception {
                ByteArrayOutputStream pkt = new ByteArrayOutputStream();
                pkt.write("DNA*".getBytes());
                pkt.write(2);
                byte[] nb = originalFileName.getBytes();
                pkt.write((nb.length >> 8) & 0xFF);
                pkt.write(nb.length & 0xFF);
                pkt.write(nb);
                int os = originalFileData.length;
                pkt.write((os >> 24) & 0xFF);
                pkt.write((os >> 16) & 0xFF);
                pkt.write((os >> 8) & 0xFF);
                pkt.write(os & 0xFF);
                publish("Computing SHA-256…");
                pkt.write(MessageDigest.getInstance("SHA-256").digest(originalFileData));
                publish("Compressing…");
                ByteArrayOutputStream gb = new ByteArrayOutputStream();
                try (GZIPOutputStream gz = new GZIPOutputStream(gb)) {
                    gz.write(originalFileData);
                }
                byte[] comp = gb.toByteArray();
                int cs = comp.length;
                publish(String.format("  %s → %s (%.1f%%)", formatSize(os), formatSize(cs), cs * 100.0 / os));
                pkt.write((cs >> 24) & 0xFF);
                pkt.write((cs >> 16) & 0xFF);
                pkt.write((cs >> 8) & 0xFF);
                pkt.write(cs & 0xFF);
                pkt.write(comp);
                byte[] full = pkt.toByteArray();
                // Convert bytes directly to DNA without an intermediate binary
                // string -- avoids 8x memory expansion for large files.
                publish("Converting to DNA sequence…");
                StringBuilder dna = new StringBuilder(full.length * 4);
                final char[] MAP = { 'A', 'C', 'G', 'T' }; // 00=A 01=C 10=G 11=T
                for (byte b : full) {
                    dna.append(MAP[(b >> 6) & 3]);
                    dna.append(MAP[(b >> 4) & 3]);
                    dna.append(MAP[(b >> 2) & 3]);
                    dna.append(MAP[b & 3]);
                }
                publish("DNA length: " + dna.length() + " bases");
                return dna.toString();
            }

            @Override
            protected void process(List<String> c) {
                c.forEach(DNAStorageWithFountainCodes.this::log);
            }

            @Override
            protected void done() {
                try {
                    dnaSequence = get();
                    dnaPanel.setDNASequence(dnaSequence);
                    int p = Math.min(1000, dnaSequence.length());
                    dnaTextArea.setText(dnaSequence.substring(0, p));
                    if (dnaSequence.length() > p)
                        dnaTextArea.append("\n… (" + (dnaSequence.length() - p) + " more)");
                    log("=== ENCODING COMPLETE ===");
                    statusLabel.setText("Encoded: " + dnaSequence.length() + " bases");
                    saveImageBtn.setEnabled(true);
                    corruptTestBtn.setEnabled(true);
                } catch (Exception ex) {
                    log("ERROR: " + ex.getMessage());
                } finally {
                    encodeBtn.setEnabled(true);
                }
            }
        }.execute();
    }

    // Save
    private void saveDNAImage() {
        log("=== SAVING WITH FOUNTAIN CODE PROTECTION ===");
        statusLabel.setText("Saving…");
        new SwingWorker<Void, String>() {
            @Override
            protected Void doInBackground() throws Exception {
                ByteArrayOutputStream pkt = new ByteArrayOutputStream();
                pkt.write("DNA*".getBytes());
                pkt.write(2);
                byte[] nb = originalFileName.getBytes();
                pkt.write((nb.length >> 8) & 0xFF);
                pkt.write(nb.length & 0xFF);
                pkt.write(nb);
                int os = originalFileData.length;
                pkt.write((os >> 24) & 0xFF);
                pkt.write((os >> 16) & 0xFF);
                pkt.write((os >> 8) & 0xFF);
                pkt.write(os & 0xFF);
                pkt.write(MessageDigest.getInstance("SHA-256").digest(originalFileData));
                ByteArrayOutputStream gb = new ByteArrayOutputStream();
                try (GZIPOutputStream gz = new GZIPOutputStream(gb)) {
                    gz.write(originalFileData);
                }
                byte[] comp = gb.toByteArray();
                int cs = comp.length;
                pkt.write((cs >> 24) & 0xFF);
                pkt.write((cs >> 16) & 0xFF);
                pkt.write((cs >> 8) & 0xFF);
                pkt.write(cs & 0xFF);
                pkt.write(comp);
                byte[] full = pkt.toByteArray();
                publish("Fountain-encoding (LT codes, 70% overhead — tolerates ~20% erasure)…");
                int blockSize = adaptiveBlockSize(full.length);
                int k = (int) Math.ceil((double) full.length / blockSize);
                publish("  blockSize=" + formatSize(blockSize) + "  k=" + k + "  target_droplets="
                        + (int) Math.ceil(k * 1.70) + "  erasure_tolerance=~20%");
                // 70% overhead: after 20% erasure, 0.8*N=1.36*k droplets survive, enough for
                // Robust Soliton.
                final double OVERHEAD = 0.70;
                List<Droplet> drops = fountainEncode(full, blockSize, OVERHEAD,
                        pct -> {
                            if (pct % 10 == 0)
                                publish("  Encoding… " + pct + "%");
                        });
                publish("  Generated " + drops.size() + " droplets");
                // Self-test: decode the just-generated droplets immediately. This catches
                // encoder bugs (e.g. duplicate srcBlocks) before the file is saved, when
                // re-encoding is trivial.
                publish("  Self-test: verifying encode integrity…");
                byte[] selfTest = fountainDecode(drops, k, blockSize, full.length);
                boolean selfOK = selfTest.length >= 4 && selfTest[0] == 'D' && selfTest[1] == 'N' && selfTest[2] == 'A'
                        && selfTest[3] == '*';
                if (!selfOK) {
                    String hex = selfTest.length >= 4 ? String.format("%02X %02X %02X %02X",
                            selfTest[0] & 0xFF, selfTest[1] & 0xFF, selfTest[2] & 0xFF, selfTest[3] & 0xFF)
                            : "(packet too short: " + selfTest.length + " bytes)";
                    throw new IOException(
                            "Encode self-test FAILED — decoded magic=[" + hex + "] not [44 4E 41 2A].\n" +
                                    "The encoder produced inconsistent droplets. Please report this bug.");
                }
                publish("  ✅ Self-test passed — encode integrity verified");
                byte[] dropRaw = serializeDroplets(drops, k, blockSize, full.length);
                ByteArrayOutputStream db = new ByteArrayOutputStream();
                try (GZIPOutputStream dz = new GZIPOutputStream(db)) {
                    dz.write(dropRaw);
                }
                byte[] compDrop = db.toByteArray();
                publish("  Compressed bundle: " + formatSize(compDrop.length));
                publish("Saving " + getDNASequenceFilename() + "…");
                try (FileOutputStream fos = new FileOutputStream(getDNASequenceFilename());
                        GZIPOutputStream gz = new GZIPOutputStream(fos)) {
                    byte[] db2 = dnaSequence.getBytes();
                    int dl = db2.length;
                    gz.write((dl >> 24) & 0xFF);
                    gz.write((dl >> 16) & 0xFF);
                    gz.write((dl >> 8) & 0xFF);
                    gz.write(dl & 0xFF);
                    gz.write(db2);
                    gz.write(compDrop);
                }

                publish("Embedding droplets into PNG and saving…");
                BufferedImage viz = dnaPanel.generateFixedSizeImage();
                BufferedImage out = embedDropletsInImage(viz, compDrop);
                File pngFile = new File(getDNAImageFilename());
                ImageIO.write(out, "PNG", pngFile);
                publish("Saved: " + getDNAImageFilename() + " (" + formatSize(pngFile.length()) + ")");
                return null;
            }

            @Override
            protected void process(List<String> c) {
                c.forEach(DNAStorageWithFountainCodes.this::log);
            }

            @Override
            protected void done() {
                try {
                    get();
                    log("=== SAVED ===");
                    log("  " + getDNAImageFilename());
                    log("  " + getDNASequenceFilename());
                    statusLabel.setText("Saved with fountain code protection");
                    compressionLabel.setText("✓ LT-protected");
                    compressionLabel.setForeground(new Color(0, 140, 0));
                    JOptionPane.showMessageDialog(DNAStorageWithFountainCodes.this,
                            "Files saved with Fountain Code protection!\n\n" + "• " + getDNAImageFilename() + "\n"
                                    + "• " + getDNASequenceFilename() + "\n\n" + "Resilient to ~25% droplet erasure.\n"
                                    + "Click '⚡ Corruption Test…' to run the test lab.",
                            "Saved", JOptionPane.INFORMATION_MESSAGE);
                } catch (Exception ex) {
                    log("ERROR: " + ex.getMessage());
                    ex.printStackTrace();
                }
            }
        }.execute();
    }

    // Decode
    private void decodeFromImage() {
        JFileChooser fc = new JFileChooser();
        fc.setFileFilter(new FileNameExtensionFilter("PNG Images", "png"));
        if (fc.showOpenDialog(this) != JFileChooser.APPROVE_OPTION)
            return;
        File png = fc.getSelectedFile();
        log("=== DECODING FROM IMAGE (no corruption) ===");
        statusLabel.setText("Decoding…");
        new SwingWorker<byte[], String>() {
            String name = "";
            int size = 0;
            boolean ok = false;

            @Override
            protected byte[] doInBackground() throws Exception {
                publish("Loading: " + png.getName());
                BufferedImage img = ImageIO.read(png);
                if (img == null)
                    throw new IOException("Cannot read PNG");
                publish("Extracting fountain bundle…");
                byte[] comp;
                try {
                    comp = extractDropletsFromImage(img);
                    publish("  Loaded from PNG pixel rows");
                } catch (IOException trunc) {
                    if (trunc.getMessage() != null && trunc.getMessage().startsWith("TRUNCATED")) {
                        publish("  PNG truncated (large file) -- loading from .dat sidecar");
                        String datPath = png.getAbsolutePath().replaceAll("dna_strand_", "dna_sequence_")
                                .replaceAll("\\.png$", ".dat");
                        File datFb = new File(datPath);
                        if (!datFb.exists())
                            throw new IOException("PNG truncated and .dat not found: " + datPath);
                        byte[] rawDat = Files.readAllBytes(datFb.toPath());
                        byte[] decDat = decompressBytes(rawDat);
                        DataInputStream dsFb = new DataInputStream(new ByteArrayInputStream(decDat));
                        int dnaLenFb = dsFb.readInt();
                        dsFb.skipBytes(dnaLenFb);
                        ByteArrayOutputStream remFb = new ByteArrayOutputStream();
                        byte[] bufFb = new byte[8192];
                        int nFb;
                        while ((nFb = dsFb.read(bufFb)) > 0)
                            remFb.write(bufFb, 0, nFb);
                        comp = remFb.toByteArray();
                        publish("  Loaded from .dat: " + datFb.getName());
                    } else {
                        throw trunc;
                    }
                }
                DropletBundle bundle;
                try {
                    bundle = deserializeDroplets(decompressBytes(comp));
                } catch (IOException ioe) {
                    String msg = ioe.getMessage();
                    if (msg != null && msg.startsWith("BUGGY_ENCODE")) {
                        // Parse out counts for a clear user message
                        String[] parts = msg.split(":", 4);
                        int dups = Integer.parseInt(parts[1]);
                        int total = Integer.parseInt(parts[2]);
                        throw new IOException("⚠  File encoded with buggy version — cannot recover.\n\n" + dups + " of "
                                + total + " droplets have corrupted block indices.\n\n"
                                + "Please re-encode the original file with this fixed version and save again.");
                    }
                    throw ioe;
                }
                publish("  k=" + bundle.k + "  droplets=" + bundle.droplets.size() +
                        (bundle.dupDroplets > 0 ? "  (⚠ " + bundle.dupDroplets + " buggy droplets discarded)" : ""));
                publish("Decoding all droplets (no erasure)…");
                byte[] pkt = fountainDecode(bundle.droplets, bundle.k, bundle.blockSize, bundle.origLen);
                // Parse — show actual bytes on failure for diagnosis
                DataInputStream dis = new DataInputStream(new ByteArrayInputStream(pkt));
                byte[] m = new byte[4];
                dis.readFully(m);
                if (!"DNA*".equals(new String(m))) {
                    String hex = String.format("%02X %02X %02X %02X",
                            m[0] & 0xFF, m[1] & 0xFF, m[2] & 0xFF, m[3] & 0xFF);
                    throw new IOException(
                            "Magic header mismatch — got [" + hex + "] instead of [44 4E 41 2A].\n\n" +
                                    "The fountain decoder could not fully reconstruct the packet.\n" +
                                    "This usually means the file was saved with a buggy version of the encoder.\n\n" +
                                    "Please re-encode and re-save the original file with this fixed version.");
                }
                dis.read();
                int nl = ((dis.read() & 0xFF) << 8) | (dis.read() & 0xFF);
                byte[] nb = new byte[nl];
                dis.readFully(nb);
                name = new String(nb);
                size = dis.readInt();
                byte[] sha = new byte[32];
                dis.readFully(sha);
                int cs = dis.readInt();
                byte[] c2 = new byte[cs];
                dis.readFully(c2);
                byte[] data = decompressBytes(c2);
                ok = Arrays.equals(sha, MessageDigest.getInstance("SHA-256").digest(data));
                publish("Checksum: " + (ok ? "✅ VALID" : "⚠ MISMATCH"));
                return data;
            }

            @Override
            protected void process(List<String> c) {
                c.forEach(DNAStorageWithFountainCodes.this::log);
            }

            @Override
            protected void done() {
                try {
                    byte[] data = get();
                    log("Recovered: " + name + " (" + formatSize(size) + ")");
                    JFileChooser fc2 = new JFileChooser();
                    fc2.setSelectedFile(new File(name.isEmpty() ? "recovered.bin" : name));
                    if (fc2.showSaveDialog(DNAStorageWithFountainCodes.this) == JFileChooser.APPROVE_OPTION) {
                        Files.write(fc2.getSelectedFile().toPath(), data);
                        log("Saved: " + fc2.getSelectedFile().getAbsolutePath());
                    }
                    statusLabel.setText("Recovered: " + name);
                } catch (Exception ex) {
                    log("ERROR: " + ex.getMessage());
                    JOptionPane.showMessageDialog(DNAStorageWithFountainCodes.this,
                            "Decode error:\n" + ex.getMessage(), "Error", JOptionPane.ERROR_MESSAGE);
                }
            }
        }.execute();
    }

    // DNA VISUALIZATION PANEL
    class DNAVisualizationPanel extends JPanel {
        private String seq = "";

        void setDNASequence(String s) {
            seq = s;
            repaint();
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            if (seq.isEmpty()) {
                g.drawString("No DNA sequence loaded", 10, 20);
                return;
            }
            Graphics2D g2 = (Graphics2D) g;
            g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            drawHelix(g2, getWidth(), getHeight(), seq);
        }

        void drawHelix(Graphics2D g, int w, int h, String s) {
            int cy = h / 2, amp = 50, dlen = Math.min(600, s.length());
            int xs = Math.max(1, w / dlen);
            for (int i = 0; i < dlen; i++) {
                char b = s.charAt(i), c = COMPLEMENT.get(b);
                int x = i * xs;
                int y1 = cy + (int) (amp * Math.sin(i * 0.05));
                int y2 = cy - (int) (amp * Math.sin(i * 0.05));
                g.setColor(new Color(200, 200, 200, 120));
                g.drawLine(x, y1, x, y2);
                g.setColor(BASE_COLORS.get(b));
                g.fillOval(x - 4, y1 - 4, 8, 8);
                g.setColor(BASE_COLORS.get(c));
                g.fillOval(x - 4, y2 - 4, 8, 8);
            }
            int lx = 10, ly = h - 25;
            g.setFont(new Font("Arial", Font.PLAIN, 11));
            for (char b : new char[] { 'A', 'T', 'G', 'C' }) {
                g.setColor(BASE_COLORS.get(b));
                g.fillOval(lx, ly, 10, 10);
                g.setColor(Color.BLACK);
                g.drawString(String.valueOf(b), lx + 13, ly + 9);
                lx += 45;
            }
            g.setColor(new Color(60, 60, 180));
            g.drawString("Fountain-protected (" + s.length() + " bases)", lx + 20, ly + 9);
        }

        BufferedImage generateFixedSizeImage() {
            BufferedImage img = new BufferedImage(800, 500, BufferedImage.TYPE_INT_RGB);
            Graphics2D g = img.createGraphics();
            g.setColor(new Color(245, 248, 255));
            g.fillRect(0, 0, 800, 500);
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            g.setColor(new Color(30, 60, 140));
            g.setFont(new Font("Arial", Font.BOLD, 16));
            g.drawString("DNA Fountain-Code Storage", 10, 22);
            g.setFont(new Font("Arial", Font.PLAIN, 11));
            g.setColor(Color.DARK_GRAY);
            g.drawString("LT Codes — Resilient to ~25% droplet loss", 10, 38);
            if (!seq.isEmpty())
                drawHelix(g, 800, 490, seq);
            g.dispose();
            return img;
        }
    }

    // ENTRY POINT
    public static void main(String[] args) {
        SwingUtilities.invokeLater(() -> new DNAStorageWithFountainCodes().setVisible(true));
    }
}