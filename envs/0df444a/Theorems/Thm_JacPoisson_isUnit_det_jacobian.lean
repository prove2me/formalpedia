-- Prove2me | Theorems.Thm_JacPoisson_isUnit_det_jacobian
-- name    : JacPoisson.isUnit_det_jacobian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:49.546834+00:00
-- url     : https://prove2.me/theorems/c801c57d-9fd9-42fb-96eb-080a75c64809
-- title:
--   Jac Poisson: is Unit det jacobian
-- statement:
--   A polynomial map preserving the canonical bracket on the generators has a unit Jacobian
--   determinant.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L61-L75
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L61-L75

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]

theorem JacPoisson.isUnit_det_jacobian (F : RegularFunction R (l ⊕ l) (l ⊕ l))
    (hF : ∀ v w, poissonBracket (F v) (F w) = poissonBracket (X v) (X w)) :
    IsUnit F.Jacobian.det := by sorry
