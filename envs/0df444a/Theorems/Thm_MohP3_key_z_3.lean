-- Prove2me | Theorems.Thm_MohP3_key_z_3
-- name    : MohP3.key_z_3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:55:10.271508+00:00
-- url     : https://prove2.me/theorems/8ad12de7-9562-5d48-b05c-48af169394ee
-- title:
--   Moh P3: key z 3
-- statement:
--   The Moh P3 construction uses the key z 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L151-L156
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L151-L156

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_z_3 : (18 : R) * (z * hh 3) - ∑ j, iota (QZ 3 j) * hh j ∈ P := by sorry
