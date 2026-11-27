-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_f2_mem_span
-- name    : MohP3.HilbertBurch.f2_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:38.157859+00:00
-- url     : https://prove2.me/theorems/adc8e806-099b-584e-a230-755e069e4a88
-- title:
--   Hilbert Burch: f2 mem span
-- statement:
--   The Hilbert Burch construction uses the f2 mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L331-L332
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L331-L332

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

theorem MohP3.HilbertBurch.f2_mem_span (x y z : A) : Gen.f2 x y z ∈ Ideal.span (Set.range (fvec x y z)) := by sorry
