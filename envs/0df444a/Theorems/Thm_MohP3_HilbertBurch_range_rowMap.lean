-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_range_rowMap
-- name    : MohP3.HilbertBurch.range_rowMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:14:06.553143+00:00
-- url     : https://prove2.me/theorems/cf5f54c7-2695-5081-ad4c-91471c1412ba
-- title:
--   Hilbert Burch: range row Map
-- statement:
--   The image of the generator map is the span of the generators.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L383-L389
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L383-L389

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

theorem MohP3.HilbertBurch.range_rowMap (x y z : A) :
    LinearMap.range (rowMap (fvec x y z)) = (Gen.P x y z : Submodule A A) := by sorry
