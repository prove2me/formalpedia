-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegral_integrable_iteratedFDeriv_param
-- name    : GlobalTheory.SchwartzIntegral.integrable_iteratedFDeriv_param
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:47:37.959223+00:00
-- url     : https://prove2.me/theorems/41c18819-f6c9-4a96-8761-96c12e2c9b5d
-- title:
--   Schwartz Integral: integrable iterated FDeriv param
-- statement:
--   The Schwartz Integral construction uses the integrable iterated FDeriv param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFunctionalIntegralComm.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFunctionalIntegralComm.lean#L64-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.SchwartzIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

theorem GlobalTheory.SchwartzIntegral.integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν := by sorry
