-- Prove2me | Theorems.Thm_MohP3_Gen_mem_of_nsmul_mem
-- name    : MohP3.Gen.mem_of_nsmul_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:09.434166+00:00
-- url     : https://prove2.me/theorems/0b702060-1b09-4a13-a4ec-78d5607e0ed7
-- title:
--   Gen: mem of nsmul mem
-- statement:
--   Over a `ℚ`-algebra a nonzero natural number is invertible, so it may be
--   cancelled from an ideal membership.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L78-L87
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L78-L87

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

theorem MohP3.Gen.mem_of_nsmul_mem [Algebra ℚ A] {I : Ideal A} {n : ℕ} (hn : n ≠ 0) {g : A}
    (h : (n : A) * g ∈ I) : g ∈ I := by sorry
