-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_mono
-- name    : MohP3.Wt.yOrd_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:47.024149+00:00
-- url     : https://prove2.me/theorems/e8572f36-923d-4b6d-b6ca-c70d4ce1e41d
-- title:
--   Wt: y Ord mono
-- statement:
--   The Wt construction uses the y Ord mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L126-L127
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L126-L127

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

theorem MohP3.Wt.yOrd_mono {p : PowerSeries k} {m n : ℕ} (h : n ≤ m) (hp : YOrd p m) : YOrd p n := by sorry
