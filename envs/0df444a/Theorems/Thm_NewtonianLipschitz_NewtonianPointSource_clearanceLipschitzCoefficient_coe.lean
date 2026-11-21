-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_clearanceLipschitzCoefficient_coe
-- name    : NewtonianLipschitz.NewtonianPointSource.clearanceLipschitzCoefficient_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:03.996945+00:00
-- url     : https://prove2.me/theorems/d3404a4f-3a12-41b9-a1e9-ab308b837855
-- title:
--   Newtonian Point Source: clearance Lipschitz Coefficient coe
-- statement:
--   Public coefficient equation, for use across opaque Lean module
--   boundaries. In particular, the bound is *computed* from d and M.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L29-L37
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConvexBaseline.lean#L29-L37

module
public import Definitions.Def_NewtonianLipschitz_BaselineBounds
public import Definitions.Def_NewtonianLipschitz_Clearance
public import Definitions.Def_NewtonianLipschitz_ConvexBaseline
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.clearanceLipschitzCoefficient_coe
    (d : ℝ) (M : ℝ≥0) (hd : 0 < d) :
    ((NewtonianPointSource.clearanceLipschitzCoefficient d M hd : ℝ≥0) : ℝ) =
      10 * (M : ℝ) / d ^ 3 := by sorry
