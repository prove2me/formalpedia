-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_formula
-- name    : NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:22:32.332447+00:00
-- url     : https://prove2.me/theorems/c96086db-c87c-4b99-8324-d17da0563d3c
-- title:
--   Newtonian Point Source: acceleration Field eq formula
-- statement:
--   The exact Cartesian field formula, exposed across sealed Lean module
--   boundaries without requiring downstream unfolding of the definition.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L39-L43
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Field.lean#L39-L43

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_formula
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x =
      (-(c.gravitationalParameter) / euclideanRadius x ^ 3) • x := by sorry
