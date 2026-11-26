-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_iotaS
-- name    : MohP3.FormalLocal.psi_iotaS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:57:17.712419+00:00
-- url     : https://prove2.me/theorems/21c03462-3191-4214-9d9e-b75558d3ba1d
-- title:
--   Formal Local: psi iota S
-- statement:
--   The Formal Local construction uses the psi iota S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L99-L106
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L99-L106

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

theorem MohP3.FormalLocal.psi_iotaS (q : PowerSeries k) : psi k (iotaS k q) = exp8 k q := by sorry
