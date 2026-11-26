-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_f4
-- name    : MohP3.FormalLocal.psi_f4
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:32.187807+00:00
-- url     : https://prove2.me/theorems/5247bb20-1db3-49fc-9790-200d3d557bb3
-- title:
--   Formal Local: psi f4
-- statement:
--   The Formal Local construction uses the psi f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L136-L138
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L136-L138

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

theorem MohP3.FormalLocal.psi_f4 : psi k (Gen.f4 (xs k) (ys k) (zs k)) = 0 := by sorry
