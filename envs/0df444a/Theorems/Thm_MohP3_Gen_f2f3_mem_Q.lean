-- Prove2me | Theorems.Thm_MohP3_Gen_f2f3_mem_Q
-- name    : MohP3.Gen.f2f3_mem_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:24.355419+00:00
-- url     : https://prove2.me/theorems/5aa8e8c4-9cf5-482b-a79f-d595c350f4fb
-- title:
--   Gen: f2f3 mem Q
-- statement:
--   The Gen construction uses the f2f3 mem Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L233-L237
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L233-L237

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

theorem MohP3.Gen.f2f3_mem_Q : f2 x y z * f3 x y z ∈ Q x y z := by sorry
