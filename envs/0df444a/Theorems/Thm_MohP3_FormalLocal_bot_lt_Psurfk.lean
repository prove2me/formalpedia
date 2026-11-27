-- Prove2me | Theorems.Thm_MohP3_FormalLocal_bot_lt_Psurfk
-- name    : MohP3.FormalLocal.bot_lt_Psurfk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:37.369084+00:00
-- url     : https://prove2.me/theorems/74557d7e-45bc-535e-b4d8-e40424575ebb
-- title:
--   Formal Local: bot lt Psurfk
-- statement:
--   The Formal Local construction uses the bot lt Psurfk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L218-L219
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L218-L219

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

theorem MohP3.FormalLocal.bot_lt_Psurfk : (⊥ : Ideal (Sk k)) < Psurfk k := by sorry
