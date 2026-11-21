-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_full
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:26:10.870614+00:00
-- url     : https://prove2.me/theorems/79d88f83-41f3-4bca-bab6-804d900e7e58
-- title:
--   Newtonian Point Source: acceleration Field fderiv full
-- statement:
--   The Newtonian Point Source construction uses the acceleration Field fderiv full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L171-L181
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L171-L181

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_full
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.accelerationField x) h =
      (-(c.gravitationalParameter) / euclideanRadius x ^ 3) • h +
        ((3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
            ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) • x := by sorry
