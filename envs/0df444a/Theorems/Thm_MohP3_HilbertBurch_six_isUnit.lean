-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_six_isUnit
-- name    : MohP3.HilbertBurch.six_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:14:10.654799+00:00
-- url     : https://prove2.me/theorems/aacd0b44-5ac8-41b9-80ec-efa5d5aa44ae
-- title:
--   Hilbert Burch: six is Unit
-- statement:
--   The Hilbert Burch construction uses the six is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L364-L366
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L364-L366

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

theorem MohP3.HilbertBurch.six_isUnit : IsUnit (6 : MvPolynomial (Fin 3) k) := by sorry
