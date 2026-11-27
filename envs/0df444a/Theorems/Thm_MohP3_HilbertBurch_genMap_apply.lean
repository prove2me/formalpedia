-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_genMap_apply
-- name    : MohP3.HilbertBurch.genMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:41:42.881966+00:00
-- url     : https://prove2.me/theorems/4dd813e7-6e72-46a5-b3f1-57bad0b9306b
-- title:
--   Hilbert Burch: gen Map apply
-- statement:
--   The Hilbert Burch construction uses the gen Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L413-L416
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L413-L416

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

theorem MohP3.HilbertBurch.genMap_apply (a : Fin 4 → S k) :
    genMap k a = a 0 * Gen.f1 (X 0) (X 1) (X 2) + a 1 * Gen.f2 (X 0) (X 1) (X 2) +
      a 2 * Gen.f3 (X 0) (X 1) (X 2) + a 3 * Gen.f4 (X 0) (X 1) (X 2) := by sorry
