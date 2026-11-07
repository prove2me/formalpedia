-- Prove2me | Theorems.Thm_MonDepMW_theorem_3_5
-- name    : MonDepMW.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:44.679726+00:00
-- url     : https://prove2.me/theorems/a76aa60e-b80b-490b-a3ee-bdaf05a93340
-- title:
--   Theorem 3.5 — from partition merge-width to merge-width
-- statement:
--   Let $r\geqslant1$, let $G$ be a graph with shatter function $\pi_G$, and let $k$ be the radius-$(6r+1)$ partition merge-width of $G$. Then $G$ has radius-$r$ merge-width at most $k\cdot\pi_G(k)$. Moreover, given a partition sequence for $G$ of radius-$(6r+1)$ width $k$, a merge sequence for $G$ of radius-$r$ width at most $k\cdot\pi_G(k)$ can be computed in $\mathcal O(n^3)$ time, where $n$ is the vertex count of $G$.
--
--   This result of Drabik et al. is the last step of the goal's proof.
--
--   **Formalization Note** $k$ is exact in both sentences; read as an upper bound the statement would fail since $\pi_G(k)=0$ for $k>n$. One program serves all $r$ and $G$, with an absolute constant. Input: $n$, adjacency matrix, $r$, $m$, the blocks of labels.
--
--   Differences from the source:
--   - reading: 𝒪(n³) time, given a partition sequence of any length m → c·(n³ + m·n + 1) steps, and word size above b·(⌊log₂(n+r+m+2)⌋+1); reason: m is not bounded in n, as consecutive partitions may coincide, and the input has m·n label cells; the paper implicitly has sequences of length O(n²) or less (in the goal m ≤ 2 + log₂ n), where this is exactly 𝒪(n³)
--   - encoding: 𝒪(n³) → absolute c, with +1; reason: 𝒪 hides constant factors (p.11); +1 only matters at n = 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
--   - reading: given a partition sequence for G of radius-(6r + 1) width k (k named in the first sentence as the partition merge-width) → any partition sequence S, with k := its exact radius-(6r + 1) width S.width; reason: the sentence can be read either way; this is the stronger reading (an optimal S gives the other), and the one the proof of Theorem 1.1 (p.17) uses, on a sequence that need not be optimal
--   - generalization: an algorithm for the r fixed by the statement → one program for every r ≥ 1, with r given as an input word and c absolute; reason: the 𝒪(n³) carries no subscript (convention of p.11), so its constant does not depend on r; writing a fixed r into the input gives the per-r algorithm of the source
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 3.5, p.14; App. A, p.39

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_MergeSeq
import Definitions.Def_MonDepMW_PartitionSeq

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Theorem 3.5.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.14 ([11, Theorem 5.1]; the algorithm in App. A, p.39): "Let r ∈ N, G be a graph, and
π_G : N → N be the shatter function of G. Let k be the radius-(6r + 1) partition merge-width of G. Then G has radius-r
merge-width at most k · π_G(k). Moreover, given a partition sequence for G of radius-(6r + 1) width k, a merge sequence
for G of radius-r width at most k · π_G(k) can be computed in 𝒪(n³) time, where n is the vertex count of G."

**Formalization Note.** `k` is exact in both sentences. Read as an upper bound the statement would fail, since
`π_G(k) = 0` for `k > n`. The input sequence has `m · n` label cells and `m` is not bounded in `n` (consecutive partitions
may coincide), so the time is `c · (n³ + m·n + 1)`, the extra term being the cost of reading the input, and the word size
accounts for `m` and `r`. One program serves every `r` and `G`, with `c` absolute. Input: `n`, adjacency matrix, `r`, `m`,
the `m` blocks of labels. -/
theorem theorem_3_5 :
    (∀ r : ℕ, 1 ≤ r → ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      MergeWidthLE G r
        (partitionMergeWidth G (6 * r + 1) * shatterFn G (partitionMergeWidth G (6 * r + 1)))) ∧
    ∃ (P : List Instr) (b c : ℕ), ∀ r : ℕ, 1 ≤ r → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : PartitionSeq n),
      S.IsValid → ∀ W : ℕ, b * (Nat.log2 (n + r + S.m + 2) + 1) ≤ W →
        RunsWithin P W (c * (n ^ 3 + S.m * n + 1))
          (graphInput G ++ [(r : ℤ)] ++ encodePartSeq S.m S.P) fun out =>
            (decodeMergeSeq n out).IsFor G ∧
            (decodeMergeSeq n out).WidthLE r
              (S.width G (6 * r + 1) * shatterFn G (S.width G (6 * r + 1))) := by sorry

end MonDepMW
