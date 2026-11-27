-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_xEquiv_f1
-- name    : MohP3.HilbertBurch.xEquiv_f1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:13:49.338399+00:00
-- url     : https://prove2.me/theorems/97576257-11c0-45b2-b68a-3cced23a2633
-- title:
--   Hilbert Burch: x Equiv f1
-- statement:
--   The Hilbert Burch construction uses the x Equiv f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L345-L349
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L345-L349

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

theorem MohP3.HilbertBurch.xEquiv_f1 :
    (xEquiv (Gen.f1 (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) k)).Monic := by sorry
