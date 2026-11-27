-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_range_fvec
-- name    : MohP3.HilbertBurch.range_fvec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:05.841897+00:00
-- url     : https://prove2.me/theorems/84b9208a-86ea-5d35-9bfd-76f80d3d058d
-- title:
--   Hilbert Burch: range fvec
-- statement:
--   The Hilbert Burch construction uses the range fvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L304-L309
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L304-L309

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

theorem MohP3.HilbertBurch.range_fvec (x y z : A) :
    Set.range (fvec x y z) = {Gen.f1 x y z, Gen.f2 x y z, Gen.f3 x y z, Gen.f4 x y z} := by sorry
