-- Prove2me | Theorems.Thm_MohP3_iotaK_C
-- name    : MohP3.iotaK_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:06.6158+00:00
-- url     : https://prove2.me/theorems/eb042b30-3531-542b-a86a-1e6d7724e983
-- title:
--   Moh P3: iota K C
-- statement:
--   The Moh P3 construction uses the iota K C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L84-L84
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L84-L84

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.iotaK_C (a : k) : iotaK k (Polynomial.C a) = MvPolynomial.C a := by sorry
