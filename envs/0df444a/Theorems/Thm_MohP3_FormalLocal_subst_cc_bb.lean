-- Prove2me | Theorems.Thm_MohP3_FormalLocal_subst_cc_bb
-- name    : MohP3.FormalLocal.subst_cc_bb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:04.965865+00:00
-- url     : https://prove2.me/theorems/8572e04f-aafc-45d3-a1ea-066b4b41825e
-- title:
--   Formal Local: subst cc bb
-- statement:
--   The Formal Local construction uses the subst cc bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L113-L125
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L113-L125

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

theorem MohP3.FormalLocal.subst_cc_bb (s : Fin 3) : MvPowerSeries.subst (cc k) (bb k s) = aa k s := by sorry
