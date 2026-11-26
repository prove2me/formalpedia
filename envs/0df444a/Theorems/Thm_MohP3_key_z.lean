-- Prove2me | Theorems.Thm_MohP3_key_z
-- name    : MohP3.key_z
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:55:54.764169+00:00
-- url     : https://prove2.me/theorems/e8a46389-424b-45ce-9913-19ba3fa59165
-- title:
--   Moh P3: key z
-- statement:
--   The Moh P3 construction uses the key z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L190-L192
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L190-L192

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_z (i : Fin 8) : (18 : R) * (z * hh i) - ∑ j, iota (QZ i j) * hh j ∈ P := by sorry
