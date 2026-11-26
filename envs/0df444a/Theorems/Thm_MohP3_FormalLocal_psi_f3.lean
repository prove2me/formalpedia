-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_f3
-- name    : MohP3.FormalLocal.psi_f3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:37.924212+00:00
-- url     : https://prove2.me/theorems/7362dad5-afb7-4d86-ade0-55faed5b1a93
-- title:
--   Formal Local: psi f3
-- statement:
--   The Formal Local construction uses the psi f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L131-L133
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L131-L133

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

theorem MohP3.FormalLocal.psi_f3 : psi k (Gen.f3 (xs k) (ys k) (zs k)) = 0 := by sorry
