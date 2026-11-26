-- Prove2me | Theorems.Thm_MohP3_FormalLocal_order_vvS
-- name    : MohP3.FormalLocal.order_vvS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:54:29.858301+00:00
-- url     : https://prove2.me/theorems/8e2288c9-e3fe-4766-81f2-7a78d0dc233a
-- title:
--   Formal Local: order vv S
-- statement:
--   The Formal Local construction uses the order vv S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L198-L211
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L198-L211

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

theorem MohP3.FormalLocal.order_vvS (i : Fin 8) : (vvS k i).order = (ooS i : ℕ∞) := by sorry
