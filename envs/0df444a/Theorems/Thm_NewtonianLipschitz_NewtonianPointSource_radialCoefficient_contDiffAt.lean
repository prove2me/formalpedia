-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_contDiffAt
-- name    : NewtonianLipschitz.NewtonianPointSource.radialCoefficient_contDiffAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:56.840123+00:00
-- url     : https://prove2.me/theorems/3f59cfec-fdf4-427d-8049-0d5dc71da889
-- title:
--   Newtonian Point Source: radial Coefficient cont Diff At
-- statement:
--   The Newtonian Point Source construction uses the radial Coefficient cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L54-L81
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Derivative.lean#L54-L81

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.radialCoefficient_contDiffAt
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 c.radialCoefficient x := by sorry
