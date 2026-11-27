-- Prove2me | Theorems.Thm_MohP3_key_z_2
-- name    : MohP3.key_z_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:41.02886+00:00
-- url     : https://prove2.me/theorems/8095a84a-47d0-4854-ad8e-fd9ce08e8d75
-- title:
--   Moh P3: key z 2
-- statement:
--   The Moh P3 construction uses the key z 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L144-L149
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L144-L149

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_z_2 : (18 : R) * (z * hh 2) - ∑ j, iota (QZ 2 j) * hh j ∈ P := by sorry
