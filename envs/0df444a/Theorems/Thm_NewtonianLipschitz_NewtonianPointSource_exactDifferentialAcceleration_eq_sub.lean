-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_exactDifferentialAcceleration_eq_sub
-- name    : NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:22.509178+00:00
-- url     : https://prove2.me/theorems/7d2f9470-de3a-402e-a599-fa9ee93b9972
-- title:
--   Newtonian Point Source: exact Differential Acceleration eq sub
-- statement:
--   Public unfolding identity for the exact nonlinear two-position
--   differential force. Later modules can use this equality without
--   unfolding the imported definition.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L57-L62
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L57-L62

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_eq_sub
    (c : NewtonianPointSource) (q : Vec3) :
    c.exactDifferentialAcceleration q =
      c.accelerationField (c.displacement + q) -
        c.accelerationField c.displacement := by sorry
