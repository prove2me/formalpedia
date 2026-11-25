-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Superpos_fderiv_int_apply
-- name    : GlobalTheory.RealWeil.Superpos.fderiv_int_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:53.364334+00:00
-- url     : https://prove2.me/theorems/514f151c-9c59-41ba-82b4-e1ff3f29e74d
-- title:
--   Superpos: fderiv int apply
-- statement:
--   The Superpos construction uses the fderiv int apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L149-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L149-L158

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

theorem GlobalTheory.RealWeil.Superpos.fderiv_int_apply (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v z : V) :
    fderiv ℝ (fun v => ∫ y, itg om ρ ι h g v y ∂ν) v z =
      (∫ y, itg om ρ ι (dh om ι h z) g v y ∂ν) + ∫ y, itg om ρ ι h (fun w => fderiv ℝ g w z) v y ∂ν := by sorry
