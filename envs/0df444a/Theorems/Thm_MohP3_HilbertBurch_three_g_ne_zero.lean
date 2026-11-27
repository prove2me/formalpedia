-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_three_g_ne_zero
-- name    : MohP3.HilbertBurch.three_g_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:57.639254+00:00
-- url     : https://prove2.me/theorems/54c38071-7a70-4b78-bd28-ef7c2241fa74
-- title:
--   Hilbert Burch: three g ne zero
-- statement:
--   The Hilbert Burch construction uses the three g ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L359-L362
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L359-L362

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

theorem MohP3.HilbertBurch.three_g_ne_zero : (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) ≠ 0 := by sorry
