-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_g_mem
-- name    : MohP3.HilbertBurch.g_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:31.484694+00:00
-- url     : https://prove2.me/theorems/ae35f75c-e356-5066-9d56-cc3815e8a12d
-- title:
--   Hilbert Burch: g mem
-- statement:
--   The Hilbert Burch construction uses the g mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L337-L340
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L337-L340

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

theorem MohP3.HilbertBurch.g_mem (x y z : A) : 3 * (y ^ 5 - z ^ 4) ∈ Ideal.span (Set.range (fvec x y z)) := by sorry
