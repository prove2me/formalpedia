-- Prove2me | Theorems.Thm_MohP3_FormalLocal_order_exp8
-- name    : MohP3.FormalLocal.order_exp8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:12.300831+00:00
-- url     : https://prove2.me/theorems/4b23bf8b-5147-564d-a465-db330d5c580d
-- title:
--   Formal Local: order exp8
-- statement:
--   The Formal Local construction uses the order exp8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L225-L229
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L225-L229

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

theorem MohP3.FormalLocal.order_exp8 {q : PowerSeries k} (hq : q ≠ 0) :
    (exp8 k q).order = ((8 * q.order.toNat : ℕ) : ℕ∞) := by sorry
