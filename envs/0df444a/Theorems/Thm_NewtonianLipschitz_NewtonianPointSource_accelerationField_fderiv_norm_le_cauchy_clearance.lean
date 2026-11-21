-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_norm_le_cauchy_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_cauchy_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:26.757387+00:00
-- url     : https://prove2.me/theorems/e1b3d855-8c8c-4ebb-bec2-df4a81320e3c
-- title:
--   Newtonian Point Source: acceleration Field fderiv norm le cauchy clearance
-- statement:
--   The Newtonian Point Source construction uses the acceleration Field fderiv norm le cauchy clearance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L130-L156
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/BaselineBounds.lean#L130-L156

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_norm_le_cauchy_clearance
    (c : NewtonianPointSource) (x h : Vec3) (d M : ℝ)
    (hx : x ≠ 0) (hd : 0 < d)
    (hclear : d ≤ euclideanRadius x)
    (hM : c.gravitationalParameter ≤ M) :
    ‖(fderiv ℝ c.accelerationField x) h‖ ≤
      (M / d ^ 3) * ‖h‖ +
        (3 * M / d ^ 5) *
          (‖toPhysicalVec3 x‖ * ‖toPhysicalVec3 h‖) * ‖x‖ := by sorry
