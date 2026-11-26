-- Prove2me | Theorems.Thm_MohP3_Gen_f1f1_mem_Q
-- name    : MohP3.Gen.f1f1_mem_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:49.573002+00:00
-- url     : https://prove2.me/theorems/c50eb043-3ba6-4ff1-8a33-a4000e443c90
-- title:
--   Gen: f1f1 mem Q
-- statement:
--   The Gen construction uses the f1f1 mem Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L203-L207
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L203-L207

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

theorem MohP3.Gen.f1f1_mem_Q : f1 x y z * f1 x y z ∈ Q x y z := by sorry
