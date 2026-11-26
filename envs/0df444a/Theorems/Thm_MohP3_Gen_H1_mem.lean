-- Prove2me | Theorems.Thm_MohP3_Gen_H1_mem
-- name    : MohP3.Gen.H1_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:07.997196+00:00
-- url     : https://prove2.me/theorems/8a44f9df-ce28-59b2-a94d-b04f6d0e0b9b
-- title:
--   Gen: H1 mem
-- statement:
--   The Gen construction uses the H1 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L59-L59
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L59-L59

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

theorem MohP3.Gen.H1_mem : H1 x y z ∈ Q x y z := by sorry
