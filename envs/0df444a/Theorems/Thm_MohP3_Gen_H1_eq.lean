-- Prove2me | Theorems.Thm_MohP3_Gen_H1_eq
-- name    : MohP3.Gen.H1_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:35.266904+00:00
-- url     : https://prove2.me/theorems/cdd87a7b-d92f-576b-a4f9-dbd0b6978c4a
-- title:
--   Gen: H1 eq
-- statement:
--   The first reverse identity.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L111-L112
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generic.lean#L111-L112

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

theorem MohP3.Gen.H1_eq : H1 x y z = (-24*x)*f1 x y z + ell x y z*f3 x y z + 81*f4 x y z := by sorry
