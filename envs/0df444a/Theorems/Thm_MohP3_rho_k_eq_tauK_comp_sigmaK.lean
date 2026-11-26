-- Prove2me | Theorems.Thm_MohP3_rho_k_eq_tauK_comp_sigmaK
-- name    : MohP3.rho_k_eq_tauK_comp_sigmaK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:06:38.690703+00:00
-- url     : https://prove2.me/theorems/86a488b9-190f-5101-9a85-223038c43d81
-- title:
--   Moh P3: rho k eq tau K comp sigma K
-- statement:
--   The Moh P3 construction uses the rho k eq tau K comp sigma K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L59-L62
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L59-L62

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

theorem MohP3.rho_k_eq_tauK_comp_sigmaK : rho_k k = (tauK k).comp (sigmaK k) := by sorry
