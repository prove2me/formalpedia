-- Prove2me | Theorems.Thm_MohP3_Ppoly_mem_minimalPrimes_Qpoly
-- name    : MohP3.Ppoly_mem_minimalPrimes_Qpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:49.430874+00:00
-- url     : https://prove2.me/theorems/33003796-8650-42fc-b115-8b78e345bd67
-- title:
--   Moh P3: Ppoly mem minimal Primes Qpoly
-- statement:
--   `Ppoly k` is a minimal prime of `Qpoly k`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L31-L32
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L31-L32

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

theorem MohP3.Ppoly_mem_minimalPrimes_Qpoly : Ppoly k ∈ (Qpoly k).minimalPrimes := by sorry
