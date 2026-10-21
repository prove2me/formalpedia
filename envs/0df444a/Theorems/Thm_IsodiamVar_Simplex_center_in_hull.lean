-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_center_in_hull
-- name    : IsodiamVar.Simplex.center_in_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:12.993052+00:00
-- url     : https://prove2.me/theorems/3793e457-a0ae-4353-95f8-8a5b882f750b
-- title:
--   Proof of Theorem 1.10 — minimizing center lies in the support hull
-- statement:
--   Let $K$ be compact, and let $\mu\in\mathcal P(K)$ maximize generalized variance for a radial function $V(x)=v(\|x\|)$, where $v$ is nonnegative, convex and strictly increasing on $[0,\infty)$. If $z_*$ minimizes the recentering integral, then
--
--   $$
--   z_*\in\overline{\operatorname{conv}}(\operatorname{spt}\mu).
--   $$
--
--   This places the optimizing center inside the support's closed convex hull, as used in the equality analysis.
--
--   **Formalization Note** The paper translates $z_*$ to the origin; the statement is translation invariant. Strict increase makes the closer-point contradiction valid.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 15, proof of Theorem 1.10, center-in-hull claim

import Mathlib
import Definitions.Def_IsodiamVar_Simplex_Defs

open MeasureTheory

namespace IsodiamVar.Simplex

/-- The center-in-hull claim in the proof of Theorem 1.10, before translation. -/
theorem center_in_hull {n : ℕ} (K : Set (E n)) (hK : IsCompact K)
    (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ t → 0 ≤ v t)
    (hvconv : ConvexOn ℝ (Set.Ici 0) v) (hvmono : StrictMonoOn v (Set.Ici 0))
    (μ : Measure (E n)) (hμ : InP K μ)
    (hmax : ∀ ν : Measure (E n), InP K ν →
      varV (fun x => v ‖x‖) ν ≤ varV (fun x => v ‖x‖) μ) (zs : E n)
    (hzs : IsMinOn (fun z => ∫ x, v ‖x - z‖ ∂μ) Set.univ zs) :
    zs ∈ closedConvexHull ℝ μ.support := by sorry

end IsodiamVar.Simplex
