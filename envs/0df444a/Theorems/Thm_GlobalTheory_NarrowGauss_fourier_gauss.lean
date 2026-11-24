-- Prove2me | Theorems.Thm_GlobalTheory_NarrowGauss_fourier_gauss
-- name    : GlobalTheory.NarrowGauss.fourier_gauss
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:57:51.500869+00:00
-- url     : https://prove2.me/theorems/5418cd61-56a3-41f0-93f8-b2e93d6be803
-- title:
--   Narrow Gauss: fourier gauss
-- statement:
--   The Narrow Gauss construction uses the fourier gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NarrowGaussConvolutionDense.lean#L32-L38

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

theorem GlobalTheory.NarrowGauss.fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by sorry
