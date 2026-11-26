-- Prove2me | Theorems.Thm_MohP3_key_x_3
-- name    : MohP3.key_x_3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:54:51.512594+00:00
-- url     : https://prove2.me/theorems/c313ab24-54d3-4c16-b7a8-c187d7769c20
-- title:
--   Moh P3: key x 3
-- statement:
--   The Moh P3 construction uses the key x 3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L95-L100
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L95-L100

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x_3 : (18 : R) * (x * hh 3) - ∑ j, iota (QX 3 j) * hh j ∈ P := by sorry
