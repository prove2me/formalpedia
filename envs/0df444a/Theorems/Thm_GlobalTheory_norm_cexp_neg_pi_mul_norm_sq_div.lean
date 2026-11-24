-- Prove2me | Theorems.Thm_GlobalTheory_norm_cexp_neg_pi_mul_norm_sq_div
-- name    : GlobalTheory.norm_cexp_neg_pi_mul_norm_sq_div
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:19.764892+00:00
-- url     : https://prove2.me/theorems/91e6756b-c5c2-4ef8-8467-9211c498b63e
-- title:
--   Global Theory: norm cexp neg pi mul norm sq div
-- statement:
--   The Global Theory construction uses the norm cexp neg pi mul norm sq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L178-L184

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
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.norm_cexp_neg_pi_mul_norm_sq_div (b : ℂ) (v : E) :
    ‖Complex.exp (-π * ‖v‖ ^ 2 / b)‖ = Real.exp (-(π * b⁻¹.re) * ‖v‖ ^ 2) := by sorry
