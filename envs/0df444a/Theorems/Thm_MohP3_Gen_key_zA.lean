-- Prove2me | Theorems.Thm_MohP3_Gen_key_zA
-- name    : MohP3.Gen.key_zA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:15.949828+00:00
-- url     : https://prove2.me/theorems/be7f172a-f2f5-567b-9b89-d833a2de388f
-- title:
--   Gen: key z A
-- statement:
--   Multiplication by `z` on the eight generators, modulo the curve ideal.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L318-L323
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L318-L323

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

theorem MohP3.Gen.key_zA (i : Fin 8) :
    (18 : A) * (z * hh x y z i) =
      (∑ j, qzA y i j * hh x y z j) + ∑ j, wzA x y z i j * ff x y z j := by sorry
