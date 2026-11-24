-- Prove2me | Theorems.Thm_GlobalTheory_fourier_cexp_neg_pi_mul_norm_sq_add
-- name    : GlobalTheory.fourier_cexp_neg_pi_mul_norm_sq_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:24.230943+00:00
-- url     : https://prove2.me/theorems/71e6c1b9-037f-41c1-beb4-a0aad3d6c053
-- title:
--   Global Theory: fourier cexp neg pi mul norm sq add
-- statement:
--   The Global Theory construction uses the fourier cexp neg pi mul norm sq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L186-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L186-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))

theorem GlobalTheory.fourier_cexp_neg_pi_mul_norm_sq_add {b : ℂ} (hb : 0 < b.re) (w y : E) :
    𝓕 (fun v : E ↦ Complex.exp (-π * b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪w, v⟫)) y =
      b ^ (-(finrank ℝ E / 2 : ℂ)) * Complex.exp (-π * ‖y - w‖ ^ 2 / b) := by sorry
