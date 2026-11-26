-- Prove2me | Theorems.Thm_MohP3_iota_X
-- name    : MohP3.iota_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:28.059625+00:00
-- url     : https://prove2.me/theorems/0e3f2145-ec79-4a29-8cdc-0551056d382e
-- title:
--   Moh P3: iota X
-- statement:
--   The Moh P3 construction uses the iota X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L36-L36
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Closure.lean#L36-L36

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.iota_X : iota Polynomial.X = y := by sorry
