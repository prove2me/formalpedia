-- Prove2me | Theorems.Thm_MohP3_Wt_yOrd_monomial
-- name    : MohP3.Wt.yOrd_monomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:00:14.841025+00:00
-- url     : https://prove2.me/theorems/4cfb25b6-f48e-4c08-bce9-8b05bdf37ae6
-- title:
--   Wt: y Ord monomial
-- statement:
--   A monomial `c * y^e` has weighted order at least `n` as soon as `n ≤ 8e`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L173-L175
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L173-L175

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

theorem MohP3.Wt.yOrd_monomial (c : k) (e n : ℕ) (h : n ≤ 8 * e) :
    YOrd (PowerSeries.C c * (PowerSeries.X : PowerSeries k) ^ e) n := by sorry
