-- Prove2me | Theorems.Thm_MohP3_K_comp_X8_ne_zero
-- name    : MohP3.K.comp_X8_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:57.663801+00:00
-- url     : https://prove2.me/theorems/4b89e0c0-5505-5ec3-a6d9-d7fbe3452e73
-- title:
--   K: comp X8 ne zero
-- statement:
--   The K construction uses the comp X8 ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L45-L50
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L45-L50

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

theorem MohP3.K.comp_X8_ne_zero {p : Polynomial k} (hp : p ≠ 0) : p.comp (X ^ 8) ≠ 0 := by sorry
