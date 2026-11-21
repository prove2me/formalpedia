-- Prove2me | Theorems.Thm_NewtonianLipschitz_physicalNewtonianAcceleration_contDiffAt
-- name    : NewtonianLipschitz.physicalNewtonianAcceleration_contDiffAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:31.422183+00:00
-- url     : https://prove2.me/theorems/8adc8f9b-b66e-4b90-aef2-d1ee7565759c
-- title:
--   Newtonian Lipschitz: physical Newtonian Acceleration cont Diff At
-- statement:
--   The physical Newtonian central field is continuously differentiable
--   at every nonzero separation. In contrast, no smoothness at the
--   collision point is asserted.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L31-L47
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Smoothness.lean#L31-L47

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.physicalNewtonianAcceleration_contDiffAt
    (μ : ℝ) (q : PhysicalVec3) (hq : q ≠ 0) :
    ContDiffAt ℝ 1 (physicalNewtonianAcceleration μ) q := by sorry
