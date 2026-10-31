-- Prove2me | Theorems.Thm_MultimodularDocks_fact_1
-- name    : MultimodularDocks.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:40.199184+00:00
-- url     : https://prove2.me/theorems/915e74df-4f3d-47dd-a449-aa373d2fff6a
-- title:
--   Fact 1 (corrected: Definition 1 on the quadrant) — for fixed docks, cost is convex in the number of bikes
-- statement:
--   Let $f$ be multimodular and fix a number $n$ of docks. Then $k\mapsto f(n-k,k)$ is convex on $\{0,1,\dots,n\}$: for $1\le k\le n-1$,
--
--   $$
--   2f(n-k,k)\le f(n-k+1,k-1)+f(n-k-1,k+1).
--   $$
--
--   In particular, for any demand profile, a station's UDF with its number of docks fixed is convex in the number of bikes. This is what makes greedy placement of bikes (Algorithm 1) correct.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: c_i(d + b − k, k) for the UDF c_i of any demand profile, with l_i ≤ d + b ≤ u_i → f(n − k, k) for any f multimodular on the quadrant, any n; reason: the page proves it by adding (2) and (3); the UDF is multimodular by Lemma 2.1, and the band condition only ensures finiteness, which holds for real f
--   - encoding: convex in k ∈ {0, 1, …, d + b} → nonnegative second differences at 1 ≤ k ≤ n − 1; reason: the standard characterization of convexity of a function on an integer interval
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, App. C.1, Fact 1, p.44

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

namespace MultimodularDocks

/-- **Fact 1** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, App. C.1, Fact 1, p.44). For a
multimodular `f` and a fixed number `n` of docks, `k ↦ f (n − k) k` is convex on
`{0, 1, …, n}`: for `1 ≤ k ≤ n − 1`,
`2 f(n − k, k) ≤ f(n − k + 1, k − 1) + f(n − k − 1, k + 1)`.

**Formalization Note** The page states it for the UDF `c_i` of any demand profile with
`l_i ≤ d + b ≤ u_i`; it is stated here for every multimodular `f`, which covers `c_i` by
Lemma 2.1 (and is how the page proves it: "follows by adding inequalities (2) and (3)").
Convexity of a function on `{0, …, n}` is the nonnegativity of its second differences at the
interior points. -/
theorem fact_1 (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (n k : ℤ) (hk : 1 ≤ k)
    (hkn : k + 1 ≤ n) :
    2 * f (n - k) k ≤ f (n - k + 1) (k - 1) + f (n - k - 1) (k + 1) := by sorry

end MultimodularDocks
