-- Prove2me | Theorems.Thm_MohP3_Ppoly_isPrime
-- name    : MohP3.Ppoly_isPrime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:04:31.485311+00:00
-- url     : https://prove2.me/theorems/aae0872d-28fb-45f9-9e87-1211762b1cf0
-- title:
--   Moh P3: Ppoly is Prime
-- statement:
--   The curve ideal is prime over any characteristic-zero field.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L282-L282
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L282-L282

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

theorem MohP3.Ppoly_isPrime : (Ppoly k).IsPrime := by sorry
