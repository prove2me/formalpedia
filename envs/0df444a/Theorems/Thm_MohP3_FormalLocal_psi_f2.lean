-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_f2
-- name    : MohP3.FormalLocal.psi_f2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:21.658949+00:00
-- url     : https://prove2.me/theorems/e9a3ffa6-7a08-464d-9664-bf09eb01a705
-- title:
--   Formal Local: psi f2
-- statement:
--   The Formal Local construction uses the psi f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L126-L128
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L126-L128

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

theorem MohP3.FormalLocal.psi_f2 : psi k (Gen.f2 (xs k) (ys k) (zs k)) = 0 := by sorry
