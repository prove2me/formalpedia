-- Prove2me | Theorems.Thm_JacPoisson_jacobian_id
-- name    : JacPoisson.jacobian_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:58.928172+00:00
-- url     : https://prove2.me/theorems/e7ea13c2-40b2-4428-a4a7-5ec209cc5d5d
-- title:
--   Jac Poisson: jacobian id
-- statement:
--   The Jacobian of the identity map is the identity matrix.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L54-L57
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L54-L57

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
omit [Fintype l]

theorem JacPoisson.jacobian_id : (RegularFunction.id R (l ⊕ l)).Jacobian = 1 := by sorry
