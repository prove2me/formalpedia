-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzIntegral_clm_apply_eq_integral
-- name    : GlobalTheory.SchwartzIntegral.clm_apply_eq_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:48:07.176171+00:00
-- url     : https://prove2.me/theorems/1fde53e1-5f92-40b1-9ea4-0884d489683c
-- title:
--   Schwartz Integral: clm apply eq integral
-- statement:
--   The Schwartz Integral construction uses the clm apply eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFunctionalIntegralComm.lean#L126-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzFunctionalIntegralComm.lean#L126-L181

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

theorem GlobalTheory.SchwartzIntegral.clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by sorry
