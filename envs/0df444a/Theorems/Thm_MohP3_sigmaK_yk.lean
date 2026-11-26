-- Prove2me | Theorems.Thm_MohP3_sigmaK_yk
-- name    : MohP3.sigmaK_yk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:05.003383+00:00
-- url     : https://prove2.me/theorems/da36f10c-b849-5565-a572-edcb7fa8c608
-- title:
--   Moh P3: sigma K yk
-- statement:
--   The Moh P3 construction uses the sigma K yk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L68-L69
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L68-L69

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

theorem MohP3.sigmaK_yk : sigmaK k (yk k) = (X 1 : MvPolynomial (Fin 2) k)^4 := by sorry
