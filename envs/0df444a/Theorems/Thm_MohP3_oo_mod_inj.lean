-- Prove2me | Theorems.Thm_MohP3_oo_mod_inj
-- name    : MohP3.oo_mod_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:44.276259+00:00
-- url     : https://prove2.me/theorems/fa84e38d-018e-44b6-97cd-db6d51655142
-- title:
--   Moh P3: oo mod inj
-- statement:
--   The Moh P3 construction uses the oo mod inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L74-L75
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Independence.lean#L74-L75

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3

theorem MohP3.oo_mod_inj {i j : Fin 8} (h : oo i % 8 = oo j % 8) : i = j := by sorry
