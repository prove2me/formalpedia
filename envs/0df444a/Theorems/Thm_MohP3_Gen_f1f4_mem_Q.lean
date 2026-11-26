-- Prove2me | Theorems.Thm_MohP3_Gen_f1f4_mem_Q
-- name    : MohP3.Gen.f1f4_mem_Q
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:49:10.308383+00:00
-- url     : https://prove2.me/theorems/e583920c-53d4-497b-89c1-fd504956a707
-- title:
--   Gen: f1f4 mem Q
-- statement:
--   The Gen construction uses the f1f4 mem Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L221-L225
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L221-L225

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

theorem MohP3.Gen.f1f4_mem_Q : f1 x y z * f4 x y z ∈ Q x y z := by sorry
