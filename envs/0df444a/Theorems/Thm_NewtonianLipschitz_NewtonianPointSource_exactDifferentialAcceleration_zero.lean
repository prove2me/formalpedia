-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_exactDifferentialAcceleration_zero
-- name    : NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:39.002619+00:00
-- url     : https://prove2.me/theorems/6a1082e3-c776-4a6b-82a4-f4193f285906
-- title:
--   Newtonian Point Source: exact Differential Acceleration zero
-- statement:
--   Every exact differential force, including this Newtonian one,
--   vanishes at coincident positions. This is an exact identity, not
--   a linearization claim.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L67-L71
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L67-L71

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_zero
    (c : NewtonianPointSource) :
    c.exactDifferentialAcceleration 0 = 0 := by sorry
