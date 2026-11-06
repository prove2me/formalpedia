-- Prove2me | Theorems.Thm_MenuPricing_lemma_C_3
-- name    : MenuPricing.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:55.190965+00:00
-- url     : https://prove2.me/theorems/6580eb33-ba35-4071-873a-f259a185da12
-- title:
--   Lemma C.3 — segment tree decomposition
-- statement:
--   Let $N \ge 1$ and $p_0 < p_1 < \dots < p_N$. The segment tree $\mathcal T$ built by Subroutine 4 on $p_0, \dots, p_N$
--
--   1. has $2N - 1$ tree intervals,
--   2. in at most $\lceil \log_2 N\rceil + 1$ depths, and
--   3. tree intervals of the same depth are disjoint.
--
--   Moreover, for any $0 \le i < j \le N$, the tree decomposition $\mathcal I_{\mathcal T}[p_i, p_j)$ partitions $[p_i, p_j)$ into tree intervals, at most two of each depth.
--
--   Hence any interval between endpoints is a disjoint union of $O(\log N)$ tree intervals, which bounds the error of the revenue estimates (5) of Algorithm 2.
--
--   Differences from the source:
--   - encoding: tree intervals → index triples $(i, j, h)$ for $[p_i, p_j)$ at depth $h$; "$2N-1$ tree intervals" → the index pairs are distinct and there are $2N-1$ of them; reason: with strictly increasing endpoints, distinct index pairs are distinct intervals
--   - reading: $N$ → $N \ge 1$; reason: for $N = 0$ the root $[p_0, p_0)$ is empty and Algorithm 2 builds no tree
--   - encoding: $p_0 < \dots < p_N$ → $p : \mathbb N \to \mathbb R$ strictly increasing on $\{0, \dots, N\}$; reason: Lean convention, same data
-- source:
--   Dai, Lin, Slivkins, The Power of Two Choices in Dynamic Pricing (manuscript, sha256 2dbec470…), Lemma C.3, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_MenuPricing_segTree

namespace MenuPricing

open Set

/-- Lemma C.3 (Dai, Lin, Slivkins, manuscript sha256 2dbec470…, p.45). The segment tree `𝒯` built by
Subroutine 4 on `p_0 < p_1 < ⋯ < p_N` has `2N − 1` tree intervals in at most `⌈log₂ N⌉ + 1`
depths, and tree intervals of the same depth are disjoint. Moreover, for any `0 ≤ i < j ≤ N`,
`ℐ_𝒯[p_i, p_j)` partitions `[p_i, p_j)` into tree intervals, at most two of each depth.

**Formalization Note** `𝒯 = segTree 0 N 0`, a list of `(i, j, h)` = `[p_i, p_j)` at depth `h`;
"`2N − 1` tree intervals" is: the index pairs are distinct and there are `2N − 1` of them;
`ℐ_𝒯[p_i, p_j) = decomp 0 N 0 i j`. `N ≥ 1` (for `N = 0` the root `[p_0, p_0)` is empty and
Algorithm 2 builds no tree). -/
theorem lemma_C_3 (N : ℕ) (hN : 1 ≤ N) (p : ℕ → ℝ) (hp : StrictMonoOn p (Iic N)) :
    (((segTree 0 N 0).map fun t => (t.1, t.2.1)).Nodup ∧ (segTree 0 N 0).length = 2 * N - 1) ∧
      ((segTree 0 N 0).map fun t => t.2.2).toFinset.card ≤ ⌈Real.logb 2 N⌉₊ + 1 ∧
      (∀ s ∈ segTree 0 N 0, ∀ t ∈ segTree 0 N 0, s ≠ t → s.2.2 = t.2.2 →
        Disjoint (Ico (p s.1) (p s.2.1)) (Ico (p t.1) (p t.2.1))) ∧
      ∀ i j : ℕ, i < j → j ≤ N →
        (∀ t ∈ decomp 0 N 0 i j, t ∈ segTree 0 N 0) ∧
        (decomp 0 N 0 i j).Nodup ∧
        (decomp 0 N 0 i j).Pairwise
          (fun s t => Disjoint (Ico (p s.1) (p s.2.1)) (Ico (p t.1) (p t.2.1))) ∧
        (⋃ t ∈ decomp 0 N 0 i j, Ico (p t.1) (p t.2.1)) = Ico (p i) (p j) ∧
        ∀ h : ℕ, ((decomp 0 N 0 i j).filter fun t => t.2.2 = h).length ≤ 2 := by sorry

end MenuPricing
