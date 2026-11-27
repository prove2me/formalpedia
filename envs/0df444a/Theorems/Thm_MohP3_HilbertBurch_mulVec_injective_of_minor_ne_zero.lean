-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_mulVec_injective_of_minor_ne_zero
-- name    : MohP3.HilbertBurch.mulVec_injective_of_minor_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:11:36.940491+00:00
-- url     : https://prove2.me/theorems/26e21ccd-21c2-47bb-a81c-9793856808f4
-- title:
--   Hilbert Burch: mul Vec injective of minor ne zero
-- statement:
--   If some maximal minor of `Φ` is nonzero, the map `Φ : S^3 → S^4` is injective.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L123-L139
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L123-L139

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
variable {S : Type*} [CommRing S] [IsDomain S]

theorem MohP3.HilbertBurch.mulVec_injective_of_minor_ne_zero (Φ : Matrix (Fin 4) (Fin 3) S) (i : Fin 4)
    (hi : maximalMinor Φ i ≠ 0) : Function.Injective (Matrix.mulVecLin Φ) := by sorry
