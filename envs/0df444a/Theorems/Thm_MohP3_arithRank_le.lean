-- Prove2me | Theorems.Thm_MohP3_arithRank_le
-- name    : MohP3.arithRank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:12.658951+00:00
-- url     : https://prove2.me/theorems/c671d70d-255f-47d1-989c-d561fbea267c
-- title:
--   Moh P3: arith Rank le
-- statement:
--   The Moh P3 construction uses the arith Rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L39-L42
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L39-L42

module
public import Mathlib
public import Definitions.Def_MohP3_Ara
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3
variable {A : Type*} [CommRing A]

theorem MohP3.arithRank_le {I : Ideal A} (s : Finset A)
    (hs : (Ideal.span (s : Set A)).radical = I.radical) :
    arithRank I ≤ s.card := by sorry
