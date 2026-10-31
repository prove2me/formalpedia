-- Prove2me | Theorems.Thm_MultimodularDocks_local_optimal_P3
-- name    : MultimodularDocks.local_optimal_P3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:45.803931+00:00
-- url     : https://prove2.me/theorems/57527993-5ec0-43f5-81ff-64ec88f5fb9b
-- title:
--   §3.2 and implication 3 of Lemma 3.1 (corrected: Definition 1 on the quadrant) — a local optimum is optimal for (P3)
-- statement:
--   Let every station cost be multimodular and let $(\vec d,\vec b)$ be feasible. If no feasible allocation in the neighborhood $N(\vec d,\vec b)=\{o_{ij},e_{ij},E_{ijh},O_{ijh}(\vec d,\vec b): i,j,h\in[n]\}$ (with $i,j,h$ unrestricted, so that the moves of a single bike are included) has a smaller objective, then $(\vec d,\vec b)$ is optimal for (P3). This contains implication 3 of Lemma 3.1: a bike-optimal allocation with no better neighbor is optimal for (P3).
--
--   Hence, if Algorithm 3 stops because no neighbor improves, its output is optimal for the problem without operational constraint.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §3.2, p.18, and implication 3 of Lemma 3.1, p.19

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsOptimalP3
import Definitions.Def_MultimodularDocks_DockMove

namespace MultimodularDocks

/-- **A local optimum is optimal for (P3)** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §3.2,
p.18: "an allocation (d⃗, b⃗) that is locally optimal with respect to N(·, ·) must also be
globally optimal with respect to P3", and implication 3 of Lemma 3.1, p.19). Let every station
cost be multimodular and `a` be feasible. If no feasible allocation in `N(a)`, the set of all
`m.apply a` for dock-moves `m` with `i, j, h` unrestricted as on p.18, has a smaller objective,
then `a` is optimal for (P3).

**Formalization Note** The neighborhood is the page's `N(d⃗, b⃗)` with `i, j, h ∈ [n]`
unrestricted, so it contains the bike moves (`E i i h`, `O i i h`); local optimality with
respect to them gives bike-optimality (Facts 1 and 2), which is the hypothesis of
implication 3. This form implies implication 3's (bike-optimal and no better neighbor with
`i ≠ j`). -/
theorem local_optimal_P3 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a : Alloc S) (ha : Feasible I a)
    (hloc : ∀ m : DockMove S, Feasible I (m.apply a) → cost I a ≤ cost I (m.apply a)) :
    IsOptimalP3 I a := by sorry

end MultimodularDocks
