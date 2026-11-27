-- Prove2me | Theorems.Thm_MohP3_key_x_2
-- name    : MohP3.key_x_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:26.412105+00:00
-- url     : https://prove2.me/theorems/bc9ca303-9da0-5bdb-8c49-ef2c88022d30
-- title:
--   Moh P3: key x 2
-- statement:
--   The Moh P3 construction uses the key x 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L88-L93
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L88-L93

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x_2 : (18 : R) * (x * hh 2) - ∑ j, iota (QX 2 j) * hh j ∈ P := by sorry
