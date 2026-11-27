-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_span_fvec
-- name    : MohP3.HilbertBurch.span_fvec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:09.84295+00:00
-- url     : https://prove2.me/theorems/273bdd47-b11a-5d4f-b5cb-e358d1306a4e
-- title:
--   Hilbert Burch: span fvec
-- statement:
--   `J = (f1,f2,f3,f4)` is the span of the generator row.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L312-L313
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L312-L313

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

theorem MohP3.HilbertBurch.span_fvec (x y z : A) : Ideal.span (Set.range (fvec x y z)) = Gen.P x y z := by sorry
