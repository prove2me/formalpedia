-- Prove2me | Theorems.Thm_MohP3_FormalLocal_two_le_height_Pk
-- name    : MohP3.FormalLocal.two_le_height_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:44.809796+00:00
-- url     : https://prove2.me/theorems/8c184967-0b26-5c39-b1cc-1f4fb5a6fb54
-- title:
--   Formal Local: two le height Pk
-- statement:
--   The Formal Local construction uses the two le height Pk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L223-L234
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L223-L234

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

theorem MohP3.FormalLocal.two_le_height_Pk : 2 ≤ (Pk k).height := by sorry
