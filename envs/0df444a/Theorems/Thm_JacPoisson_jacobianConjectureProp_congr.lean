-- Prove2me | Theorems.Thm_JacPoisson_jacobianConjectureProp_congr
-- name    : JacPoisson.jacobianConjectureProp_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:55.772021+00:00
-- url     : https://prove2.me/theorems/1aeb1770-294c-4fca-bf32-14f9db3dd492
-- title:
--   Jac Poisson: jacobian Conjecture Prop congr
-- statement:
--   The Jacobian conjecture for one set of variables gives it for any equivalent set.
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L85-L117
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L85-L117

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
variable {k : Type*} [CommRing k] {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]

theorem JacPoisson.jacobianConjectureProp_congr (e : σ ≃ τ) (h : JacobianConjectureProp k σ) :
    JacobianConjectureProp k τ := by sorry
