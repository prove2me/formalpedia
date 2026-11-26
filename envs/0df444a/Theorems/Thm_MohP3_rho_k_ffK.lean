-- Prove2me | Theorems.Thm_MohP3_rho_k_ffK
-- name    : MohP3.rho_k_ffK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:45.412539+00:00
-- url     : https://prove2.me/theorems/e1e5fe28-ca38-44ab-a68d-2ac061ac3705
-- title:
--   Moh P3: rho k ff K
-- statement:
--   The Moh P3 construction uses the rho k ff K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L92-L105
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L92-L105

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

theorem MohP3.rho_k_ffK (j : Fin 4) : rho_k k (ffK k j) = 0 := by sorry
