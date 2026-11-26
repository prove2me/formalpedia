-- Prove2me | Theorems.Thm_MohP3_Wt_mem_En
-- name    : MohP3.Wt.mem_En
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:51:30.385429+00:00
-- url     : https://prove2.me/theorems/c0a483dc-47f7-5ffa-beea-5a7b92f9999a
-- title:
--   Wt: mem En
-- statement:
--   The Wt construction uses the mem En property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L257-L259
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean#L257-L259

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

theorem MohP3.Wt.mem_En {n : ℕ} {p : ℕ × ℕ × ℕ} (hp : p ∈ En n) :
    6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n := by sorry
