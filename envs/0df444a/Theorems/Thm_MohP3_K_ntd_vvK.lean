-- Prove2me | Theorems.Thm_MohP3_K_ntd_vvK
-- name    : MohP3.K.ntd_vvK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:35.862535+00:00
-- url     : https://prove2.me/theorems/e0d7bbd8-e16f-5600-a694-cca6695193f3
-- title:
--   K: ntd vv K
-- statement:
--   The K construction uses the ntd vv K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L70-L82
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L70-L82

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

theorem MohP3.K.ntd_vvK (i : Fin 8) : (vvK k i).natTrailingDegree = ooK i := by sorry
