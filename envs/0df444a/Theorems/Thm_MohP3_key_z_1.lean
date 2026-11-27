-- Prove2me | Theorems.Thm_MohP3_key_z_1
-- name    : MohP3.key_z_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:53.272798+00:00
-- url     : https://prove2.me/theorems/df382393-3c82-59ea-a7dd-667e957f3a81
-- title:
--   Moh P3: key z 1
-- statement:
--   The Moh P3 construction uses the key z 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L137-L142
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L137-L142

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_z_1 : (18 : R) * (z * hh 1) - ∑ j, iota (QZ 1 j) * hh j ∈ P := by sorry
