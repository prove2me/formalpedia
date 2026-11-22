-- Prove2me | Theorems.Thm_NoHair_Weyl_comparison_of_common_boundary_profile
-- name    : NoHair.Weyl.comparison_of_common_boundary_profile
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:47:26.812416+00:00
-- url     : https://prove2.me/theorems/9530da30-2348-486b-825d-7c2be5e60585
-- title:
--   Deviation and axis traces for Ernst maps with the same normalized boundary estimates
-- statement:
--   Two Ernst pairs controlled by the same positive reference scale have bounded Mazur deviation. If their normalized axial norms tend uniformly to one and their normalized twist errors tend uniformly to zero at infinity, then their deviation tends uniformly to zero as well. Where the second pair has a regular axis trace $(0,Y_*)$, the first has that same trace. On the interior of a horizon interval, a positive axial norm limit for the second pair makes every existing axial norm limit of the first strictly positive. No field equations are required for this boundary comparison.
-- source:
--   A. J. Amsel, G. T. Horowitz, D. Marolf and M. M. Roberts, Uniqueness of Extremal Kerr and Kerr–Newman Black Holes, pp. 3–5, eqs. (8)–(13), https://arxiv.org/abs/0906.2367. P. T. Chruściel, J. L. Costa and M. Heusler, Stationary Black Holes: Uniqueness and Beyond, §§8.2, 8.4, pp. 44, 47–48, eqs. (8.13), (8.24), Prop. 8.1, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_weylBoundaryProfile

open Filter Topology

namespace NoHair.Weyl

theorem comparison_of_common_boundary_profile (u v b : ErnstPotentials)
    (hb : ∀ p, 0 < b.normSq p) (hu : HasProfileEstimates u b) (hv : HasProfileEstimates v b) :
    HasComparisonBounds u v ∧ ∀ ℓ J : ℝ, HasAxisData v ℓ J →
      (∀ z : ℝ, |z| < ℓ → ∃ L : ℝ, Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 L)) →
      HasAxisData u ℓ J := by
  sorry

end NoHair.Weyl
