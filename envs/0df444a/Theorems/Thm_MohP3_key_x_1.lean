-- Prove2me | Theorems.Thm_MohP3_key_x_1
-- name    : MohP3.key_x_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:32.387501+00:00
-- url     : https://prove2.me/theorems/d5858cff-a499-4ab2-95e0-0841a4af9613
-- title:
--   Moh P3: key x 1
-- statement:
--   The Moh P3 construction uses the key x 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L81-L86
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L81-L86

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.key_x_1 : (18 : R) * (x * hh 1) - ∑ j, iota (QX 1 j) * hh j ∈ P := by sorry
