-- Prove2me | Theorems.Thm_MohP3_Gen_qzD_wt
-- name    : MohP3.Gen.qzD_wt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:01:20.43186+00:00
-- url     : https://prove2.me/theorems/5a866e10-47b2-54dc-a26c-5243fe713344
-- title:
--   Gen: qz D wt
-- statement:
--   The weight estimate for the `z`-closure matrix.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L330-L331
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L330-L331

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

theorem MohP3.Gen.qzD_wt (i j : Fin 8) : 10 + sig i ≤ 8 * (qzD i j).2 + sig j := by sorry
