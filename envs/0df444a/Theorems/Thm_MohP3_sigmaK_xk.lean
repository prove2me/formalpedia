-- Prove2me | Theorems.Thm_MohP3_sigmaK_xk
-- name    : MohP3.sigmaK_xk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:00.652398+00:00
-- url     : https://prove2.me/theorems/4549a120-1060-5d8f-8a63-fb76f0f3842e
-- title:
--   Moh P3: sigma K xk
-- statement:
--   The Moh P3 construction uses the sigma K xk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L65-L65
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L65-L65

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.sigmaK_xk : sigmaK k (xk k) = X 0 := by sorry
