-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
-- name    : MohP3.HilbertBurch.rowMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:10:23.83836+00:00
-- url     : https://prove2.me/theorems/8de9adc2-6d68-50ca-b03e-31fced19345b
-- title:
--   Hilbert Burch: row Map apply
-- statement:
--   The Hilbert Burch construction uses the row Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L76-L76
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L76-L76

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
variable {S : Type*} [CommRing S]

theorem MohP3.HilbertBurch.rowMap_apply (f : Fin 4 → S) (a : Fin 4 → S) : rowMap f a = a ⬝ᵥ f := by sorry

attribute [defeq] MohP3.HilbertBurch.rowMap_apply
