-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_f4_mem_span
-- name    : MohP3.HilbertBurch.f4_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:25.528197+00:00
-- url     : https://prove2.me/theorems/309d8bbc-9d0a-599a-a95f-a4dc99dd17a4
-- title:
--   Hilbert Burch: f4 mem span
-- statement:
--   The Hilbert Burch construction uses the f4 mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L334-L335
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L334-L335

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

theorem MohP3.HilbertBurch.f4_mem_span (x y z : A) : Gen.f4 x y z ∈ Ideal.span (Set.range (fvec x y z)) := by sorry
