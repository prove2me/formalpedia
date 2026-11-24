-- Prove2me | Theorems.Thm_GlobalTheory_GaussWidths_integral_gauss_mul_gauss
-- name    : GlobalTheory.GaussWidths.integral_gauss_mul_gauss
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:00.239403+00:00
-- url     : https://prove2.me/theorems/e7796017-02d5-43d5-b1f9-5f1941e7b006
-- title:
--   Gauss Widths: integral gauss mul gauss
-- statement:
--   The Gauss Widths construction uses the integral gauss mul gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L39-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSchwartzGaussWidth.lean#L39-L61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.GaussWidths.integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by sorry
