-- Prove2me | Theorems.Thm_MohP3_Gen_f2f2_mem_Q
-- name    : MohP3.Gen.f2f2_mem_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:17.82329+00:00
-- url     : https://prove2.me/theorems/94ff356d-17fc-46a0-85fa-31e93f82eabc
-- title:
--   Gen: f2f2 mem Q
-- statement:
--   The Gen construction uses the f2f2 mem Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L227-L231
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L227-L231

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]

theorem MohP3.Gen.f2f2_mem_Q : f2 x y z * f2 x y z ∈ Q x y z := by sorry
