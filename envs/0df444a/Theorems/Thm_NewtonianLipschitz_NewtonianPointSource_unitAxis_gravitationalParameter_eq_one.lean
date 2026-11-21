-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_gravitationalParameter_eq_one
-- name    : NewtonianLipschitz.NewtonianPointSource.unitAxis_gravitationalParameter_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:21:17.851174+00:00
-- url     : https://prove2.me/theorems/d1c90c1c-cf8d-4587-bd39-a45ac3d4ab0e
-- title:
--   Newtonian Point Source: unit Axis gravitational Parameter eq one
-- statement:
--   Expose the exact unit gravitational parameter across Lean module
--   boundaries, where the original illustrative source definition is opaque.
--   This can instantiate explicit quantitative bounds without assuming
--   an external unit-field Lipschitz coefficient.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L86-L88
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L86-L88

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.unitAxis_gravitationalParameter_eq_one :
    NewtonianPointSource.unitAxis.gravitationalParameter = 1 := by sorry
