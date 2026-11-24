-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Superpos_hasFDerivAt_itg
-- name    : GlobalTheory.RealWeil.Superpos.hasFDerivAt_itg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:54.300863+00:00
-- url     : https://prove2.me/theorems/5a7c0e34-2be2-497b-90ad-aaf0fe239a3b
-- title:
--   Superpos: has FDeriv At itg
-- statement:
--   The Superpos construction uses the has FDeriv At itg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HeisenbergSmoothRapidSuperpositionTranslates.lean#L85-L92

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

theorem GlobalTheory.RealWeil.Superpos.hasFDerivAt_itg {g : V → B} (hg : Differentiable ℝ g) (h : Y → ℂ) (v : V) (y : Y) :
    HasFDerivAt (fun w => itg om ρ ι h g w y) (dI om ρ ι h g v y) v := by sorry
