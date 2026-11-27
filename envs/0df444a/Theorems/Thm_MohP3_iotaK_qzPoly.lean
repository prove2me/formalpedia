-- Prove2me | Theorems.Thm_MohP3_iotaK_qzPoly
-- name    : MohP3.iotaK_qzPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:28.211163+00:00
-- url     : https://prove2.me/theorems/613c3283-dd84-5150-9d2a-6d94e62e63e5
-- title:
--   Moh P3: iota K qz Poly
-- statement:
--   The Moh P3 construction uses the iota K qz Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L154-L156
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L154-L156

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

theorem MohP3.iotaK_qzPoly (i j : Fin 8) : iotaK k (qzPoly k i j) = Gen.qzA (yk k) i j := by sorry
