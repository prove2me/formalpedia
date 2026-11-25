-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Superpos_contDiff_int
-- name    : GlobalTheory.RealWeil.Superpos.contDiff_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:51.50838+00:00
-- url     : https://prove2.me/theorems/989d041f-e7cf-49a1-8f72-a1b589848d3b
-- title:
--   Superpos: cont Diff int
-- statement:
--   The Superpos construction uses the cont Diff int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L160-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L160-L173

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
open GlobalTheory.RealWeil.Superpos
variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}

theorem GlobalTheory.RealWeil.Superpos.contDiff_int (hρ : IsHeis (fun x y => om x y) ρ) (n : ℕ) : ∀ h : Y → ℂ, Mom ν h → ∀ g : V → B,
    ContDiff ℝ ∞ g → ContDiff ℝ n fun v => ∫ y, itg om ρ ι h g v y ∂ν := by sorry
