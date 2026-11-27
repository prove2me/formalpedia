-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_phiMap_apply
-- name    : MohP3.HilbertBurch.phiMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:41:13.520819+00:00
-- url     : https://prove2.me/theorems/fe375a82-9426-5452-9072-987a5f7b3644
-- title:
--   Hilbert Burch: phi Map apply
-- statement:
--   The Hilbert Burch construction uses the phi Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L410-L410
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L410-L410

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

theorem MohP3.HilbertBurch.phiMap_apply (v : Fin 3 → S k) : phiMap k v = phi (X 0) (X 1) (X 2) *ᵥ v := by sorry
