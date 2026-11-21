-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:31.813805+00:00
-- url     : https://prove2.me/theorems/a9aad4be-1720-4858-b288-dcb6348a20db
-- title:
--   Newtonian Point Source: acceleration Field fderiv norm le of clearance
-- statement:
--   The true Newtonian field derivative, not an assumed auxiliary
--   field, has the following explicit *directionwise* norm bound.
--
--   The remaining steps for a full quantitative Lipschitz certificate are to
--   control the inner product by Cauchy–Schwarz, convert the Pi norm,
--   and apply the mean-value theorem on a convex collision-free domain.
--   This inequality by itself is not a uniform Lipschitz estimate.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L75-L128
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L75-L128

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_of_clearance
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (M / d ^ 3) * ‖h‖ +
        (3 * M / d ^ 5) *
          abs (⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) * ‖x‖ := by sorry
