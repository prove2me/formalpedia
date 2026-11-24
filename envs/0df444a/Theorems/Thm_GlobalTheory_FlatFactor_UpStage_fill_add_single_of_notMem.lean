-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_UpStage_fill_add_single_of_notMem
-- name    : GlobalTheory.FlatFactor.UpStage.fill_add_single_of_notMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:54.083002+00:00
-- url     : https://prove2.me/theorems/a4ce72bb-b626-4cdb-9fa6-ad988f14b422
-- title:
--   Up Stage: fill add single of not Mem
-- statement:
--   The Up Stage construction uses the fill add single of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L139-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L139-L146

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.FlatFactor.UpStage.fill_add_single_of_notMem (ev it : Finset (m × m')) (β t : Matrix m m' k) (x : {e : m × m' // e ∈ it} → k)
    (r₀ : m) (q₀ : m') (h1 : (r₀, q₀) ∉ ev) (h2 : (r₀, q₀) ∉ it) (a : k) :
    fill ev it β t x + Matrix.single r₀ q₀ a = fill ev it β (t + Matrix.single r₀ q₀ a) x := by sorry
