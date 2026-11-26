-- Prove2me | Theorems.Thm_MohP3_Wt_monomial_dd
-- name    : MohP3.Wt.monomial_dd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:00:22.609033+00:00
-- url     : https://prove2.me/theorems/008dae15-6b2f-4513-b618-0401f9814780
-- title:
--   Wt: monomial dd
-- statement:
--   The Wt construction uses the monomial dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L245-L250
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L245-L250

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

theorem MohP3.Wt.monomial_dd (a b c : ℕ) :
    (MvPowerSeries.monomial (dd a b c) (1 : k)) =
      (X 0) ^ a * (X 1) ^ b * (X 2) ^ c := by sorry
