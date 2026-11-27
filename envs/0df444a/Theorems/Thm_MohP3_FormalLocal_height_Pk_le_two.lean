-- Prove2me | Theorems.Thm_MohP3_FormalLocal_height_Pk_le_two
-- name    : MohP3.FormalLocal.height_Pk_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:42.991837+00:00
-- url     : https://prove2.me/theorems/6bb4d547-fd21-44d3-ae81-398659c503a8
-- title:
--   Formal Local: height Pk le two
-- statement:
--   The Formal Local construction uses the height Pk le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L50-L62
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L50-L62

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
open scoped Classical

theorem MohP3.FormalLocal.height_Pk_le_two : (Pk k).height ≤ 2 := by sorry
