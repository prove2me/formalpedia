-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_fourier_indicator
-- name    : GlobalTheory.GallagherLemma.fourier_indicator
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:42:55.941742+00:00
-- url     : https://prove2.me/theorems/74a0e472-dfe3-4a4d-94a7-947c25668cec
-- title:
--   Gallagher Lemma: fourier indicator
-- statement:
--   The Gallagher Lemma construction uses the fourier indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L59-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma

theorem GlobalTheory.GallagherLemma.fourier_indicator (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by sorry
