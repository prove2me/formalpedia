-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ffS_mem
-- name    : MohP3.FormalLocal.ffS_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:19.568246+00:00
-- url     : https://prove2.me/theorems/82ff5daa-0de9-5629-9f3b-282e72aabf68
-- title:
--   Formal Local: ff S mem
-- statement:
--   The Formal Local construction uses the ff S mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L59-L61
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L59-L61

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.ffS_mem (j : Fin 4) : ffS k j ∈ Pk k := by sorry
