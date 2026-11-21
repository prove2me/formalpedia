-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_fderiv_full
-- name    : NewtonianLipschitz.NewtonianPointSource.radialCoefficient_fderiv_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:17.480817+00:00
-- url     : https://prove2.me/theorems/9e054aca-1aaa-4184-9bd3-f11f319156d2
-- title:
--   Newtonian Point Source: radial Coefficient fderiv full
-- statement:
--   The Newtonian Point Source construction uses the radial Coefficient fderiv full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L101-L169
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L101-L169

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.radialCoefficient_fderiv_full
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.radialCoefficient x) h =
      (3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
        ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ := by sorry
