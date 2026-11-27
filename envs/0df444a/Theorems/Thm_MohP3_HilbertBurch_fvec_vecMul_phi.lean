-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_fvec_vecMul_phi
-- name    : MohP3.HilbertBurch.fvec_vecMul_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:36.633989+00:00
-- url     : https://prove2.me/theorems/e44aa8eb-c99a-45d8-8a59-bc5343152af9
-- title:
--   Hilbert Burch: fvec vec Mul phi
-- statement:
--   The Hilbert Burch construction uses the fvec vec Mul phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L321-L321
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L321-L321

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

theorem MohP3.HilbertBurch.fvec_vecMul_phi (x y z : A) : fvec x y z ᵥ* phi x y z = 0 := by sorry
