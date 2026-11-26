-- Prove2me | Theorems.Thm_MohP3_sigmaK_zk
-- name    : MohP3.sigmaK_zk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:11.944487+00:00
-- url     : https://prove2.me/theorems/b7e659ac-c5af-5af9-afa0-0074ce6f7ef6
-- title:
--   Moh P3: sigma K zk
-- statement:
--   The Moh P3 construction uses the sigma K zk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L72-L73
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L72-L73

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

theorem MohP3.sigmaK_zk : sigmaK k (zk k) = (X 1 : MvPolynomial (Fin 2) k)^5 := by sorry
