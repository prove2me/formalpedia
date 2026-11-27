-- Prove2me | Theorems.Thm_MohP3_key_x_4
-- name    : MohP3.key_x_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:37.892831+00:00
-- url     : https://prove2.me/theorems/cefc8a03-943c-5e29-95eb-18be5e5838ae
-- title:
--   Moh P3: key x 4
-- statement:
--   The Moh P3 construction uses the key x 4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L102-L107
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L102-L107

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x_4 : (18 : R) * (x * hh 4) - ∑ j, iota (QX 4 j) * hh j ∈ P := by sorry
