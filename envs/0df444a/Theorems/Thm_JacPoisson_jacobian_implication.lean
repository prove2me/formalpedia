-- Prove2me | Theorems.Thm_JacPoisson_jacobian_implication
-- name    : JacPoisson.jacobian_implication
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T14:50:43.677432+00:00
-- url     : https://prove2.me/theorems/90ba9bbb-c3e9-479a-818e-46418994a8bf
-- title:
--   Jac Poisson: jacobian implication
-- statement:
--   **The Jacobian conjecture in dimension `2n` implies the Poisson conjecture in dimension `n`**
--   (Adjamagbo and van den Essen, Theorem 7(1)).
--
--   Source: https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L149-L154
-- source:
--   https://github.com/zblore/fc-jacobian-poisson/blob/e395ab52d16b1c26b354daecf0c62b361f01c7a8/JacPoisson/Main.lean#L149-L154

module
public import Definitions.Def_JacPoisson_Defs
public import Definitions.Def_JacPoisson_Main
set_option autoImplicit false
@[expose] public section
public section
open JacPoisson
open MvPolynomial Matrix JacobianConjecture
open Arxiv.«math.0608009»

theorem JacPoisson.jacobian_implication {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (h : JacobianConjectureProp K (Fin (2 * n))) : PoissonConjectureFor K n := by sorry
