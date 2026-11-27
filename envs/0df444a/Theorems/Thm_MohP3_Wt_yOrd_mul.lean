-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_mul
-- name    : MohP3.Wt.yOrd_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:51:32.116805+00:00
-- url     : https://prove2.me/theorems/58092320-6080-4455-9854-28ebf7c8e65b
-- title:
--   Wt: y Ord mul
-- statement:
--   The Wt construction uses the y Ord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L150-L160
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L150-L160

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

theorem MohP3.Wt.yOrd_mul {p q : PowerSeries k} {m n : ℕ} (hp : YOrd p m) (hq : YOrd q n) :
    YOrd (p * q) (m + n) := by sorry
