-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_proposition_3_1_a
-- name    : IsodiamVar.Simplex.proposition_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:08.94211+00:00
-- url     : https://prove2.me/theorems/c2f610a2-fb65-4998-9392-8b646d47d32e
-- title:
--   Proposition 3.1(a) — radius above the simplex threshold
-- statement:
--   Let $K$ lie on the centered sphere of radius $r$ in $\mathbb R^n$, and let its diameter be at most one. If $r>r_n=\sqrt{n/(2n+2)}$, then
--
--   $$
--   0\notin\overline{\operatorname{conv}}(K).
--   $$
--
--   This gives the sharp obstruction to a diameter-constrained spherical set surrounding its center.
--
--   **Formalization Note** The paper defines $\operatorname{conv}(K)$ as the smallest closed convex set containing $K$. The sphere bounds $K$, so the real metric diameter is safe here.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 13, Proposition 3.1(a)

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

namespace IsodiamVar.Simplex

/-- Proposition 3.1(a): a radius above `rₙ` excludes the origin from the closed hull. -/
theorem proposition_3_1_a (n : ℕ) (r : ℝ) (K : Set (E n))
    (hr : rn n < r) (hKs : K ⊆ Metric.sphere (0 : E n) r)
    (hKd : Metric.diam K ≤ 1) :
    (0 : E n) ∉ closedConvexHull ℝ K := by sorry

end IsodiamVar.Simplex
