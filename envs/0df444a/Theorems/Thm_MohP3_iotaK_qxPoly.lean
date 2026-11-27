-- Prove2me | Theorems.Thm_MohP3_iotaK_qxPoly
-- name    : MohP3.iotaK_qxPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:29.705803+00:00
-- url     : https://prove2.me/theorems/241381c5-c56f-4194-bb19-db9de317d7a9
-- title:
--   Moh P3: iota K qx Poly
-- statement:
--   The Moh P3 construction uses the iota K qx Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L149-L151
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L149-L151

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

theorem MohP3.iotaK_qxPoly (i j : Fin 8) : iotaK k (qxPoly k i j) = Gen.qxA (yk k) i j := by sorry
