-- Prove2me | Theorems.Thm_MultimodularDocks_algorithm_1_bike_optimal
-- name    : MultimodularDocks.algorithm_1_bike_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:25.401153+00:00
-- url     : https://prove2.me/theorems/aed2b5a2-7371-4f0f-9768-4be4e3df8223
-- title:
--   Algorithm 1 (corrected: Definition 1 on the quadrant) — greedy bike placement terminates with a bike-optimal allocation
-- statement:
--   Let every station cost be multimodular and let $a$ be a feasible allocation. Then
--
--   1. Algorithm 1 with $\alpha=1$, started at $a$, has a complete run (it terminates), and
--   2. every allocation $y$ that a complete run from $a$ can return, under any tie-breaking, is bike-optimal and has the same number of docks as $a$ at every station.
--
--   So the first line of Algorithm 3 places the bikes optimally for the current docks.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: Algorithms 1–3 as procedures with arg max / arg min and a return statement → relations (IsBikeGreedyRun, IsGDStep, IsAlgorithm3Run) covering every tie-breaking; a stopped run is a constant sequence; reason: every execution of the pseudocode is a run of the relation and conversely; quantifying over all runs covers every tie-breaking
--   - reading: §3.1 prose: 'taking out all the bikes and then adding them one by one'; Algorithm 1 pseudocode moves one bike at a time → the pseudocode of Algorithm 1, the routine Algorithm 3 calls; reason: line 1 of Algorithm 3 applies Algorithm 1; the prose names an equivalent greedy
--   - reading: arg max on lines 3–4 when no station can receive (d_i = 0 for all i) or give (b_j = 0 for all j) a bike → the routine stops; reason: the arg max then sees only −∞ and the comparison of line 5 fails (paper.md item 9)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §3.1, p.18, and Algorithm 1, p.35 (line 12: 'If α = 1, then (d, b) is bike-optimal')

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsBikeOptimal
import Definitions.Def_MultimodularDocks_IsBikeGreedyRun

namespace MultimodularDocks

/-- **Algorithm 1 finds a bike-optimal allocation** (Freund, Henderson, Shmoys,
arXiv:1611.09304v5, §3.1, p.18, and Algorithm 1, line 12, p.35: "If α = 1, then (d⃗, b⃗) is
bike-optimal for the current allocation of docks"). If every station cost is multimodular and
`a` is feasible, then (i) Algorithm 1 with `α = 1` started at `a` terminates, and (ii) every
allocation it can return, under any tie-breaking, is bike-optimal and has the same number of
docks as `a` at every station. -/
theorem algorithm_1_bike_optimal {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a : Alloc S) (ha : Feasible I a) :
    (∃ y, IsBikeGreedyRun I a y) ∧
      ∀ y, IsBikeGreedyRun I a y →
        IsBikeOptimal I y ∧ ∀ i, dockCount y i = dockCount a i := by sorry

end MultimodularDocks
