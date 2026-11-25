-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuasiPlurisubharmonic_exp_one_le_rad
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.exp_one_le_rad
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:12.356184+00:00
-- url     : https://prove2.me/theorems/a9948c75-721e-4e4a-90e0-ffe9c6066836
-- title:
--   Quasi Plurisubharmonic: exp one le rad
-- statement:
--   The Quasi Plurisubharmonic construction uses the exp one le rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuasiPlurisubharmonic.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/QuasiPlurisubharmonic.lean#L137-L142

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuasiPlurisubharmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic

theorem GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.exp_one_le_rad {D : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas D Y}
    {L : LocPot Y} {s : Y → Y → ℂ} {m : ℕ} {W : Fin m → Set Y} (h : IsBoundary A L s W) (y : Y) :
    Real.exp 1 ≤ rad L s y := by sorry
