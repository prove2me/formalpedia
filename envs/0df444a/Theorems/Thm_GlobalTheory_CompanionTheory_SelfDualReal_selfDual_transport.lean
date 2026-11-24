-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_selfDual_transport
-- name    : GlobalTheory.CompanionTheory.SelfDualReal.selfDual_transport
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:41.27409+00:00
-- url     : https://prove2.me/theorems/76ff4108-9461-433f-a006-7ce143b382a9
-- title:
--   Self Dual Real: self Dual transport
-- statement:
--   The Self Dual Real construction uses the self Dual transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/BijectiveLinearCombinationOfRankAtStalk.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/BijectiveLinearCombinationOfRankAtStalk.lean#L9-L28

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualReal

theorem GlobalTheory.CompanionTheory.SelfDualReal.selfDual_transport {V W : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W]
    (f : V ≃+ W) (hf : Continuous f) (hf' : Continuous f.symm) (ν : Measure W) (χ : W → W → ℂ)
    (h : SelfDual ν χ) : SelfDual (ν.map f.symm) (fun x y => χ (f x) (f y)) := by sorry
