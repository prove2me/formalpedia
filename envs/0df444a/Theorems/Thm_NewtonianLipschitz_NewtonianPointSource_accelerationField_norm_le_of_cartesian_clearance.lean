-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_le_of_cartesian_clearance
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_le_of_cartesian_clearance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:43:59.143538+00:00
-- url     : https://prove2.me/theorems/f4a9372d-632f-44e4-a580-e043397988c1
-- title:
--   Newtonian Point Source: acceleration Field norm le of cartesian clearance
-- statement:
--   The magnitude of one Newtonian acceleration at a point
--   with Cartesian clearance d is at most μ / d². No convexity
--   or segment hypothesis is involved.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L37-L67
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/LongSeparation.lean#L37-L67

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_le_of_cartesian_clearance
    (c : NewtonianPointSource) (x : Vec3) (d : ℝ)
    (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    ‖c.accelerationField x‖ ≤ c.gravitationalParameter / d ^ 2 := by sorry
