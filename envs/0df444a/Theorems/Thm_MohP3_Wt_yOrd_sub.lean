-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_sub
-- name    : MohP3.Wt.yOrd_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:21:00.696568+00:00
-- url     : https://prove2.me/theorems/0bb932b5-0baf-53d6-af78-1f331cad9b06
-- title:
--   Wt: y Ord sub
-- statement:
--   The Wt construction uses the y Ord sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L137-L138
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L137-L138

module
public import Mathlib
public import Definitions.Def_MohP3_Order
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]

theorem MohP3.Wt.yOrd_sub {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p - q) n := by sorry
