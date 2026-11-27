-- Prove2me | Theorems.Thm_MohP3_Gen_wxD_wt
-- name    : MohP3.Gen.wxD_wt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:31.028456+00:00
-- url     : https://prove2.me/theorems/9e41de04-263f-42d6-bf38-e89f090a9fb2
-- title:
--   Gen: wx D wt
-- statement:
--   The weight estimate for the `x`-closure cofactors.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L334-L336
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GenClosure.lean#L334-L336

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

theorem MohP3.Gen.wxD_wt (i : Fin 8) (j : Fin 4) (t : Fin 4) :
    6 + sig i ≤ 6 * (wxD i j t).2.1 + 8 * (wxD i j t).2.2.1 + 10 * (wxD i j t).2.2.2 + tau j := by sorry
