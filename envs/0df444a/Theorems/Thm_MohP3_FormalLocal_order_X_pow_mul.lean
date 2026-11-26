-- Prove2me | Theorems.Thm_MohP3_FormalLocal_order_X_pow_mul
-- name    : MohP3.FormalLocal.order_X_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:58.72681+00:00
-- url     : https://prove2.me/theorems/89f022bf-a2ff-4f47-ad35-14cf0a4e0222
-- title:
--   Formal Local: order X pow mul
-- statement:
--   The Formal Local construction uses the order X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L193-L196
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L193-L196

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

theorem MohP3.FormalLocal.order_X_pow_mul (n : ℕ) (w : PowerSeries k) (hw : PowerSeries.coeff 0 w ≠ 0) :
    ((PowerSeries.X : PowerSeries k)^n * w).order = (n : ℕ∞) := by sorry
