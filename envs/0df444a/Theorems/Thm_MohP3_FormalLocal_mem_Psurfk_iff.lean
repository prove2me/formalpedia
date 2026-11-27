-- Prove2me | Theorems.Thm_MohP3_FormalLocal_mem_Psurfk_iff
-- name    : MohP3.FormalLocal.mem_Psurfk_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:05.929003+00:00
-- url     : https://prove2.me/theorems/1e57a1f9-922a-4a30-8fdf-83cb96c4846c
-- title:
--   Formal Local: mem Psurfk iff
-- statement:
--   The Formal Local construction uses the mem Psurfk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L141-L141
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L141-L141

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.mem_Psurfk_iff {g : Sk k} : g ∈ Psurfk k ↔ sigmaS k g = 0 := by sorry
