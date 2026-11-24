-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFamPos_summable_lamChi
-- name    : GlobalTheory.Hk.LFamPos.summable_lamChi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:21:48.421359+00:00
-- url     : https://prove2.me/theorems/89390d25-92f1-4a6f-87c5-c832c3279784
-- title:
--   LFam Pos: summable lam Chi
-- statement:
--   The LFam Pos construction uses the summable lam Chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LFamPos

theorem GlobalTheory.Hk.LFamPos.summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by sorry
