-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_UpStage_kerRed_eq
-- name    : GlobalTheory.FlatFactor.UpStage.kerRed_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:05:12.861879+00:00
-- url     : https://prove2.me/theorems/7a84fced-5bd5-47c5-98b2-590c4b94412e
-- title:
--   Up Stage: ker Red eq
-- statement:
--   The Up Stage construction uses the ker Red eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L117-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L117-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
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
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable {k : Type} [Field k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.FlatFactor.UpStage.kerRed_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ev it : Finset (m × m')) (β : Matrix m m' k) (l : SB (Matrix m m' k) →ₗ[ℂ] M) (hK : KerRed ν ev it β l)
    (Θ Θ' : SB (Matrix m m' k)) (h : ∀ t, red ν ev it β Θ.1 t = red ν ev it β Θ'.1 t) : l Θ = l Θ' := by sorry
