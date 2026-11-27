-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Pk_sq_le_Qk
-- name    : MohP3.FormalLocal.Pk_sq_le_Qk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:18:10.387927+00:00
-- url     : https://prove2.me/theorems/443ece74-ece2-56a9-a2be-99fba0928e9f
-- title:
--   Formal Local: Pk sq le Qk
-- statement:
--   The Formal Local construction uses the Pk sq le Qk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L113-L113
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L113-L113

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

theorem MohP3.FormalLocal.Pk_sq_le_Qk : Pk k ^ 2 ≤ Qk k := by sorry
