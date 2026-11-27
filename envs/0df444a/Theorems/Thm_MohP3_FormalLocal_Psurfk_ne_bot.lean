-- Prove2me | Theorems.Thm_MohP3_FormalLocal_Psurfk_ne_bot
-- name    : MohP3.FormalLocal.Psurfk_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:03.853506+00:00
-- url     : https://prove2.me/theorems/016e2cb7-b34c-46f8-a882-3e7956fea556
-- title:
--   Formal Local: Psurfk ne bot
-- statement:
--   `y^5 - z^4` is a nonzero element of `Psurfk`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L155-L178
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L155-L178

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

theorem MohP3.FormalLocal.Psurfk_ne_bot : Psurfk k ≠ ⊥ := by sorry
