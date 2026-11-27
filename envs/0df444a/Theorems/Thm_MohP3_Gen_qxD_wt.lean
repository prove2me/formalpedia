-- Prove2me | Theorems.Thm_MohP3_Gen_qxD_wt
-- name    : MohP3.Gen.qxD_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:19.509849+00:00
-- url     : https://prove2.me/theorems/1229eb6e-a245-5dfe-9e07-83a79af6011f
-- title:
--   Gen: qx D wt
-- statement:
--   The weight estimate for the `x`-closure matrix.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L326-L327
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L326-L327

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

theorem MohP3.Gen.qxD_wt (i j : Fin 8) : 6 + sig i ≤ 8 * (qxD i j).2 + sig j := by sorry
