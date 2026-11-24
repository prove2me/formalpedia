-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_continuous_fourier
-- name    : GlobalTheory.GallagherLemma.continuous_fourier
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:26.214246+00:00
-- url     : https://prove2.me/theorems/c32cbf25-0fcc-4e9b-b542-f7ee0bf94491
-- title:
--   Gallagher Lemma: continuous fourier
-- statement:
--   The Gallagher Lemma construction uses the continuous fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L7-L8

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

theorem GlobalTheory.GallagherLemma.continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) := by sorry
