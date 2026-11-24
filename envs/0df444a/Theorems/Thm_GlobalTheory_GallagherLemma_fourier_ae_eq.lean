-- Prove2me | Theorems.Thm_GlobalTheory_GallagherLemma_fourier_ae_eq
-- name    : GlobalTheory.GallagherLemma.fourier_ae_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:32.271394+00:00
-- url     : https://prove2.me/theorems/4549df2c-a239-4abb-839c-4011ca8c9c69
-- title:
--   Gallagher Lemma: fourier ae eq
-- statement:
--   The Gallagher Lemma construction uses the fourier ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegralNormSqLp.lean#L10-L29

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

theorem GlobalTheory.GallagherLemma.fourier_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by sorry
