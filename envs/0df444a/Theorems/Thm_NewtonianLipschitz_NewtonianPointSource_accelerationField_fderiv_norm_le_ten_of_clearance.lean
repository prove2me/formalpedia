-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_ten_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_ten_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:00.796205+00:00
-- url     : https://prove2.me/theorems/4d21d078-3a8f-45ec-9838-7c8082e3b031
-- title:
--   Newtonian Point Source: acceleration Field fderiv norm le ten of clearance
-- statement:
--   The Newtonian Point Source construction uses the acceleration Field fderiv norm le ten of clearance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L158-L238
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L158-L238

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_ten_of_clearance
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (10 * M / d ^ 3) * ‖h‖ := by sorry
