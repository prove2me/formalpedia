-- Prove2me | Theorems.Thm_MohP3_rho_k_iotaK
-- name    : MohP3.rho_k_iotaK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:03:14.568027+00:00
-- url     : https://prove2.me/theorems/56c5a597-ebfa-44fa-8ce3-efe291ef9170
-- title:
--   Moh P3: rho k iota K
-- statement:
--   The Moh P3 construction uses the rho k iota K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L112-L119
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L112-L119

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

theorem MohP3.rho_k_iotaK (p : Polynomial k) : rho_k k (iotaK k p) = p.comp (Polynomial.X ^ 8) := by sorry
