-- Prove2me | Theorems.Thm_MohP3_FormalLocal_psi_hhS
-- name    : MohP3.FormalLocal.psi_hhS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:35.889193+00:00
-- url     : https://prove2.me/theorems/3930c2d3-21db-5a6b-8d57-3917b0d651a7
-- title:
--   Formal Local: psi hh S
-- statement:
--   The Formal Local construction uses the psi hh S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L186-L187
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L186-L187

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

theorem MohP3.FormalLocal.psi_hhS (i : Fin 8) : psi k (hhS k i) = vvS k i := by sorry
