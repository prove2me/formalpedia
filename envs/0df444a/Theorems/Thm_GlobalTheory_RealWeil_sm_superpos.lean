-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_sm_superpos
-- name    : GlobalTheory.RealWeil.sm_superpos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:58.813275+00:00
-- url     : https://prove2.me/theorems/aca424a0-2f90-42cc-942e-acd43599b9df
-- title:
--   Real Weil: sm superpos
-- statement:
--   The Real Weil construction uses the sm superpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L177-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L177-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeisenbergSmoothRapidSuperpositionTranslates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped ContDiff Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.sm_superpos : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by sorry
