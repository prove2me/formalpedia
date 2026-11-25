-- Prove2me | Theorems.Thm_GlobalTheory_IdealChain_om_sph
-- name    : GlobalTheory.IdealChain.om_sph
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:25.622803+00:00
-- url     : https://prove2.me/theorems/11d6ff29-9197-5e88-8268-510fae70aa86
-- title:
--   Ideal Chain: om sph
-- statement:
--   The Ideal Chain construction uses the om sph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L160-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

theorem GlobalTheory.IdealChain.om_sph (μ : kˣ →* ℂˣ) (h : GL ι k) (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : om μ 1 h (sph α L' L) x = (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card ι' : ℝ) / 2) : ℝ) : ℂ) * sph α L' (act h L) x := by sorry
