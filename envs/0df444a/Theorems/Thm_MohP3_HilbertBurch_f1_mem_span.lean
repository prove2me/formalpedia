-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_f1_mem_span
-- name    : MohP3.HilbertBurch.f1_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:57.714064+00:00
-- url     : https://prove2.me/theorems/b7b5a17a-6c9b-4ae7-869c-70469f76ac17
-- title:
--   Hilbert Burch: f1 mem span
-- statement:
--   The Hilbert Burch construction uses the f1 mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L328-L329
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L328-L329

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

theorem MohP3.HilbertBurch.f1_mem_span (x y z : A) : Gen.f1 x y z ∈ Ideal.span (Set.range (fvec x y z)) := by sorry
