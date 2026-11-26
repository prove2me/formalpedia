-- Prove2me | Theorems.Thm_MohP3_FormalLocal_order_eq_coe
-- name    : MohP3.FormalLocal.order_eq_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:09.915576+00:00
-- url     : https://prove2.me/theorems/a310be44-151d-5eee-9107-2fe4c5c020b5
-- title:
--   Formal Local: order eq coe
-- statement:
--   The Formal Local construction uses the order eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L220-L222
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L220-L222

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.order_eq_coe {q : PowerSeries k} (hq : q ≠ 0) : q.order = (q.order.toNat : ℕ∞) := by sorry
