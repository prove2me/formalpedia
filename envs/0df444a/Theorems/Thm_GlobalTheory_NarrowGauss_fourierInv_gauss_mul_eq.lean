-- Prove2me | Theorems.Thm_GlobalTheory_NarrowGauss_fourierInv_gauss_mul_eq
-- name    : GlobalTheory.NarrowGauss.fourierInv_gauss_mul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:45.843907+00:00
-- url     : https://prove2.me/theorems/78f0bc0f-5379-482e-a17a-8441cd0d5773
-- title:
--   Narrow Gauss: fourier Inv gauss mul eq
-- statement:
--   The Narrow Gauss construction uses the fourier Inv gauss mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L40-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L40-L71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartzStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NarrowGaussConvolutionDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NarrowGauss
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.NarrowGauss.fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by sorry
