-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ker_psi_isPrime
-- name    : MohP3.FormalLocal.ker_psi_isPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:32.535532+00:00
-- url     : https://prove2.me/theorems/e8a3c45a-e613-50d5-8fdc-caf06f8aefcc
-- title:
--   Formal Local: ker psi is Prime
-- statement:
--   The kernel of the formal parametrization is prime, since `k[[t]]` is a
--   domain.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L154-L154
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L154-L154

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.ker_psi_isPrime : (RingHom.ker (psi k)).IsPrime := by sorry
