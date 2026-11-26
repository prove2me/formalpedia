-- Prove2me | Theorems.Thm_MohP3_Gen_f4f4_mem_Q
-- name    : MohP3.Gen.f4f4_mem_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:24.016384+00:00
-- url     : https://prove2.me/theorems/0026c08d-72c7-4999-800a-0424c0f8c398
-- title:
--   Gen: f4f4 mem Q
-- statement:
--   The Gen construction uses the f4f4 mem Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L257-L261
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L257-L261

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

theorem MohP3.Gen.f4f4_mem_Q : f4 x y z * f4 x y z ∈ Q x y z := by sorry
