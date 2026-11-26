-- Prove2me | Theorems.Thm_MohP3_key_z_0
-- name    : MohP3.key_z_0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:54:53.102225+00:00
-- url     : https://prove2.me/theorems/7075432a-e339-4ddb-9645-e4cea1031762
-- title:
--   Moh P3: key z 0
-- statement:
--   The Moh P3 construction uses the key z 0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L130-L135
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L130-L135

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_z_0 : (18 : R) * (z * hh 0) - ∑ j, iota (QZ 0 j) * hh j ∈ P := by sorry
