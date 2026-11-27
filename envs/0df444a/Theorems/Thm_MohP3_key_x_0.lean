-- Prove2me | Theorems.Thm_MohP3_key_x_0
-- name    : MohP3.key_x_0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:32.021335+00:00
-- url     : https://prove2.me/theorems/3917f1a7-4bfa-5a84-a395-17902d9fc518
-- title:
--   Moh P3: key x 0
-- statement:
--   The Moh P3 construction uses the key x 0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L74-L79
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L74-L79

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x_0 : (18 : R) * (x * hh 0) - ∑ j, iota (QX 0 j) * hh j ∈ P := by sorry
