-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_g_eq_symm
-- name    : MohP3.HilbertBurch.g_eq_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:51.033356+00:00
-- url     : https://prove2.me/theorems/28fa9bb3-3e11-54a8-a922-b2c53203b9a8
-- title:
--   Hilbert Burch: g eq symm
-- statement:
--   The Hilbert Burch construction uses the g eq symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L352-L357
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L352-L357

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.HilbertBurch.g_eq_symm :
    (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) =
      xEquiv.symm (Polynomial.C (3 * ((X 0) ^ 5 - (X 1) ^ 4))) := by sorry
