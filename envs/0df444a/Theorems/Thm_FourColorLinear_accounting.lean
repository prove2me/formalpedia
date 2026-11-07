-- Prove2me | Theorems.Thm_FourColorLinear_accounting
-- name    : FourColorLinear.accounting
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:16.322292+00:00
-- url     : https://prove2.me/theorems/726c5843-7dcf-4455-93f9-069579a15ebe
-- title:
--   Accounting: $O(n(\log\log n)^4/(\log n)^2) = o(n/\log n)$, and total $O(n/\log n)$ per Kempe change
-- statement:
--   Let $L=\log_2n$ and $r_i=s\,2^i$. On level $i$ there are $n/r_i$ regions at cost per region $1$ if $r_i\le L^2/(\log_2 L)^2$, $q_i^2$ with $q_i=\sqrt{r_i}\log_2r_i/L$ if $L^2/(\log_2 L)^2<r_i<L^2$, and $\sqrt{r_i}$ if $r_i\ge L^2$. Then, for each $\lambda>0$, there are $C,n_0$ such that for $n\ge n_0$ the following hold.
--
--   1. The intermediate levels have $\sum_i n/r_i\le Cn(\log_2 L)^2/L^2$ regions, and total time at most $Cn(\log_2 L)^4/L^2$.
--   2. The total over all levels with $\lambda L\le r_i\le n$ is at most $Cn/L$.
--
--   Moreover $(\log_2 L)^4/L^2$ divided by $1/L$ tends to $0$ as $n\to\infty$. This is the arithmetic that gives one Kempe change in $O(n/\log n)$ time.
--
--   Differences from the source:
--   - reading: "log n", "log log n" in an O-statement → Real.logb 2 throughout; reason: any fixed base changes only C
--   - generalization: leaf level ℓ = Θ(log n) → any λ > 0 with r_i ≥ λL, C depending on λ; reason: the printed ℓ is in the range
--   - reading: p.18: "we have √ri = O(ℓ)" in the range i₀ < i ≤ i₁; §2.2's table-lookup levels up to r_i = Θ(ℓ²), §3's up to (log n)²/(log log n)² → per-region costs as above, from p.14 and p.24; reason: p.24 says only the counters fall outside a look-up in the intermediate range, in O(q²) time, with q = Θ(√r_i log r_i/ℓ)
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §3.1, p.24; pp.14, 17

import Mathlib

open Filter Topology

namespace FourColorLinear

/-- The accounting of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.24, with pp.14, 17: "There are O(n(log log n)²/(log n)²) such regions,
so the total time for all these regions becomes O(n(log log n)⁴/(log n)²) = o(n/(log n)), which is fine
for the proof of Lemma 11."

**Formalization Note** `L = log₂ n`, `r_i = s·2^i`. On a level there are `n/r_i` regions, at the cost
per region of §§2.2 and 3: constant up to `r_i ≤ L²/(log L)²`, `q²` with `q = √r_i log r_i / L` in between,
`√r_i` from `L²` up. The sum runs from `r_i ≥ λL` (the leaves) to `r_i ≤ n`; `λ` is any positive constant,
and `C` depends on it. `Real.logb 2` is used throughout. p.18's "ri = O(ℓ)" is a slip for `√ri = O(ℓ)`;
p.14's values are used. -/
theorem accounting (s : ℕ) (hs : 1 ≤ s) (lam : ℝ) (hlam : 0 < lam) :
    let L : ℕ → ℝ := fun n => Real.logb 2 n
    let rr : ℕ → ℝ := fun i => s * 2 ^ i
    let cost : ℝ → ℝ → ℝ := fun l r =>
      if r ≤ l ^ 2 / (Real.logb 2 l) ^ 2 then 1
      else if r < l ^ 2 then (Real.sqrt r * Real.logb 2 r / l) ^ 2
      else Real.sqrt r
    let mid : ℕ → Finset ℕ := fun n => (Finset.range (n + 1)).filter fun i =>
      (L n) ^ 2 / (Real.logb 2 (L n)) ^ 2 < rr i ∧ rr i < (L n) ^ 2
    (Tendsto (fun n : ℕ => (Real.logb 2 (L n)) ^ 4 / (L n) ^ 2 / (1 / L n)) atTop (𝓝 0)) ∧
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n, n₀ ≤ n →
      -- the regions of the intermediate range, and their total time
      ∑ i ∈ mid n, (n : ℝ) / rr i ≤ C * n * (Real.logb 2 (L n)) ^ 2 / (L n) ^ 2 ∧
      ∑ i ∈ mid n, ((n : ℝ) / rr i) * (Real.sqrt (rr i) * Real.logb 2 (rr i) / L n) ^ 2 ≤
        C * n * (Real.logb 2 (L n)) ^ 4 / (L n) ^ 2 ∧
      -- the whole sum
      ∑ i ∈ (Finset.range (n + 1)).filter (fun i => lam * L n ≤ rr i ∧ rr i ≤ n),
          ((n : ℝ) / rr i) * cost (L n) (rr i) ≤ C * n / L n := by sorry

end FourColorLinear
