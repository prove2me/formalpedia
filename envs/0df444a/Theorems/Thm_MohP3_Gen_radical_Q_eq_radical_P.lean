-- Prove2me | Theorems.Thm_MohP3_Gen_radical_Q_eq_radical_P
-- name    : MohP3.Gen.radical_Q_eq_radical_P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:47.990606+00:00
-- url     : https://prove2.me/theorems/1c23f351-a61e-4f60-b957-d05ff24774ec
-- title:
--   Gen: radical Q eq radical P
-- statement:
--   From `P^2 ≤ Q ≤ P` the two ideals have the same radical, over any
--   `ℚ`-algebra.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L282-L289
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L282-L289

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

theorem MohP3.Gen.radical_Q_eq_radical_P : (Q x y z).radical = (P x y z).radical := by sorry
