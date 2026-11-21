-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_lipschitzOnWith_anchor_of_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_of_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:54:33.186293+00:00
-- url     : https://prove2.me/theorems/cc022a86-d2dc-476a-9b0b-a7390623bb1e
-- title:
--   Newtonian Point Source: unit Axis lipschitz On With anchor of clearance
-- statement:
--   A finite-anchor noncollision margin yields an *explicit* unit
--   field Lipschitz constant on the whole anchor ball. This is precisely
--   an explicit unit-field certificate; it is proved, not supplied.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L96-L120
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L96-L120

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_of_clearance
    (anchor : Vec3) (ρ d : ℝ) (hd : 0 < d)
    (hanchor : d + ρ ≤ dist anchor (0 : Vec3)) :
    LipschitzOnWith
      (NewtonianPointSource.clearanceLipschitzCoefficient
        d (1 : ℝ≥0) hd)
      NewtonianPointSource.unitAxis.accelerationField
      (Metric.ball anchor ρ) := by sorry
