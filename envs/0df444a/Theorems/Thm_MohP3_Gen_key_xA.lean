-- Prove2me | Theorems.Thm_MohP3_Gen_key_xA
-- name    : MohP3.Gen.key_xA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:44.177422+00:00
-- url     : https://prove2.me/theorems/a1e76e0a-a010-5422-815c-259a9d27f9be
-- title:
--   Gen: key x A
-- statement:
--   Multiplication by `x` on the eight generators, modulo the curve ideal.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L310-L315
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L310-L315

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_GenClosure
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)

theorem MohP3.Gen.key_xA (i : Fin 8) :
    (18 : A) * (x * hh x y z i) =
      (∑ j, qxA y i j * hh x y z j) + ∑ j, wxA x y z i j * ff x y z j := by sorry
