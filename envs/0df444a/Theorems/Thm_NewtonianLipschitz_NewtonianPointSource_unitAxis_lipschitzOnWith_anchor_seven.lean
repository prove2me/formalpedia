-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_lipschitzOnWith_anchor_seven
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T04:02:15.988469+00:00
-- url     : https://prove2.me/theorems/c460e23f-76de-4dad-885b-9621c5308381
-- title:
--   Newtonian Point Source: unit Axis lipschitz On With anchor seven
-- statement:
--   The improved explicit bound applies to each safe anchor ball.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L77-L93
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexImproved.lean#L77-L93

module
public import Definitions.Def_NewtonianLipschitz_ImprovedBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexImproved
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_lipschitzOnWith_anchor_seven
    (anchor : Vec3) (ρ d : ℝ) (hd : 0 < d)
    (hanchor : d + ρ ≤ dist anchor (0 : Vec3)) :
    LipschitzOnWith
      (NewtonianPointSource.sevenLipschitzCoefficient
        d (1 : ℝ≥0) hd)
      NewtonianPointSource.unitAxis.accelerationField
      (Metric.ball anchor ρ) := by sorry
