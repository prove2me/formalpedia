-- Prove2me | Theorems.Thm_MohP3_K_indepK
-- name    : MohP3.K.indepK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:02:44.174099+00:00
-- url     : https://prove2.me/theorems/47e86128-83d0-50da-aace-129427479ad2
-- title:
--   K: indep K
-- statement:
--   The eight polynomials `vvK k i` are linearly independent over `k[t^8]`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L88-L125
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L88-L125

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
variable (k) [CharZero k]

theorem MohP3.K.indepK (p : Fin 8 → Polynomial k) (hs : ∑ i, (p i).comp (X ^ 8) * vvK k i = 0) :
    ∀ i, p i = 0 := by sorry
