-- Prove2me | Theorems.Thm_MohP3_K_ooK_mod_inj
-- name    : MohP3.K.ooK_mod_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:58.966129+00:00
-- url     : https://prove2.me/theorems/6e7b9a6c-c516-422f-88d6-a97d45d7177d
-- title:
--   K: oo K mod inj
-- statement:
--   The K construction uses the oo K mod inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L84-L85
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L84-L85

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

theorem MohP3.K.ooK_mod_inj {i j : Fin 8} (h : ooK i % 8 = ooK j % 8) : i = j := by sorry
