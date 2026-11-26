-- Prove2me | Theorems.Thm_MohP3_iota_C
-- name    : MohP3.iota_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:43.286275+00:00
-- url     : https://prove2.me/theorems/faa7f317-cd5d-4b68-8b78-1a41e90f2ef2
-- title:
--   Moh P3: iota C
-- statement:
--   The Moh P3 construction uses the iota C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L38-L38
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L38-L38

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.iota_C (a : ℚ) : iota (Polynomial.C a) = MvPolynomial.C a := by sorry
