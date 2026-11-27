-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_phiMap_injective
-- name    : MohP3.HilbertBurch.phiMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:10.804892+00:00
-- url     : https://prove2.me/theorems/42992fc4-ee38-45a0-8a59-2ff28b4d27a5
-- title:
--   Hilbert Burch: phi Map injective
-- statement:
--   **1.** `Φ : S^3 → S^4` is injective.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L419-L419
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L419-L419

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

theorem MohP3.HilbertBurch.phiMap_injective : Function.Injective (phiMap k) := by sorry
