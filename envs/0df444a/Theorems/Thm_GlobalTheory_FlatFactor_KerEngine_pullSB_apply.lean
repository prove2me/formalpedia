-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_KerEngine_pullSB_apply
-- name    : GlobalTheory.FlatFactor.KerEngine.pullSB_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:41.180109+00:00
-- url     : https://prove2.me/theorems/4f083441-8471-4b76-9106-56a135f67520
-- title:
--   Ker Engine: pull SB apply
-- statement:
--   The Ker Engine construction uses the pull SB apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearMapKillsPartialEvalIntegralKernelOfLaws.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LinearMapKillsPartialEvalIntegralKernelOfLaws.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatLinearFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillsPartialEvalIntegralKernelOfLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.KerEngine

theorem GlobalTheory.FlatFactor.KerEngine.pullSB_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (Φ : SB Y) (x : X) :
    (pullSB e Φ).1 x = Φ.1 (e x) := by sorry
