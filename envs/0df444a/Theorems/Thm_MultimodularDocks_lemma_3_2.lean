-- Prove2me | Theorems.Thm_MultimodularDocks_lemma_3_2
-- name    : MultimodularDocks.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:13.79434+00:00
-- url     : https://prove2.me/theorems/76e47600-0ca5-49ab-aa64-7d7dcb36b529
-- title:
--   Lemma 3.2 (corrected: Definition 1 on the quadrant) — an improving neighbor that is closer to a better solution
-- statement:
--   Let every station cost be multimodular and let $(\vec d,\vec b)$ be bike-optimal but not optimal for (P3): some feasible $(\vec d^\star,\vec b^\star)$ has a smaller objective. Then there is a feasible $(\vec d',\vec b')\in N(\vec d,\vec b)$ that has both a smaller objective than $(\vec d,\vec b)$ and a smaller dock-move distance to $(\vec d^\star,\vec b^\star)$ than $(\vec d,\vec b)$ does.
--
--   The neighbor need not satisfy the operational constraint of (P2). Together with Lemma 3.1 this shows that a bike-optimal local optimum is optimal for (P3).
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: station costs are the UDFs c_i of demand profiles, plus the depot cost c_D (pp.9–12) → any finite family of real costs g_i that are multimodular on the quadrant; reason: the analysis uses only Definition 1 (p.12: it does not rely on monotonicity); specializes to the paper's stations [n] ∪ {D} by Lemma 2.1 (lemma_2_1) and the depot lemma (depot_multimodular)
--   - encoding: objective c = Σ c_i with c_i = +∞ off {d, b ≥ 0, l_i ≤ d + b ≤ u_i}; problems over all integer vectors → real objective cost = Σ g_i, and every allocation compared is required to be Feasible (band, |b|₁ = B, |d + b|₁ = D + B); reason: an allocation has finite objective exactly when it is feasible; no extended-real arithmetic; same instances
--   - encoding: dock-move distance |d + b − d' − b'|₁ / 2 ≤ r → dockGap ≤ 2 * r with dockGap = Σ_i |(d_i + b_i) − (d'_i + b'_i)|; reason: avoids division; same relation
--   - reading: N(d, b) with i, j, h ∈ [n] unrestricted (p.18) → Neighbor: a dock-move from i to j with i ≠ j, h free; reason: the page states that every neighbor is at |d + b − d' − b'|₁ = 2, which needs i ≠ j; for i = j the move is a bike move or the identity, which never improves a bike-optimal allocation, so no run changes (paper.md item 5)
--   - reading: 'a better allocation / solution' (d⋆, b⋆) → a P3-feasible allocation a' with cost a' < cost a; reason: the allocations compared are the feasible ones, with finite objective (paper.md item 7); equal bike totals are what excludes Cases 3.c) and 4.c) (p.46)
--   - reading: 'not optimal for either P2 or P3' → a feasible a′ with a smaller objective exists (a is not P3-optimal); reason: the lemma's next sentence names the better solution (d⋆, b⋆); a solution better within P2's constraint is also P3-feasible, so the P3 form covers both
--   - reading: (d′, b′) ∈ N(d, b) 'has a lower objective value' → n is a feasible neighbor; reason: a lower objective than a finite one is finite, i.e. feasible
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Lemma 3.2, p.19; proof App. C.2.2, p.48

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_IsBikeOptimal
import Definitions.Def_MultimodularDocks_Neighbor
import Definitions.Def_MultimodularDocks_dockGap

namespace MultimodularDocks

/-- **Lemma 3.2** (Freund, Henderson, Shmoys, arXiv:1611.09304v5, Lemma 3.2, p.19; proof
App. C.2.2, p.48). Let every station cost be multimodular, `a` bike-optimal and `a'` a feasible
allocation with a smaller objective. Then some feasible neighbor `n` of `a` has a smaller
objective than `a` and is at smaller dock-move distance to `a'` than `a` is.

**Formalization Note** As the page says, `n` is not required to satisfy the operational
constraint (the distance to the initial allocation). -/
theorem lemma_3_2 {S : Type*} [Fintype S] [DecidableEq S] (I : Instance S)
    (hg : ∀ i, IsMultimodular (I.g i)) (a a' : Alloc S) (ha : IsBikeOptimal I a)
    (ha' : Feasible I a') (hlt : cost I a' < cost I a) :
    ∃ n, Feasible I n ∧ Neighbor a n ∧ cost I n < cost I a ∧
      dockGap n a' < dockGap a a' := by sorry

end MultimodularDocks
