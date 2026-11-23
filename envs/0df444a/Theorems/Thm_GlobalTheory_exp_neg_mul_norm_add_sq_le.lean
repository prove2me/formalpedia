-- Prove2me | Theorems.Thm_GlobalTheory_exp_neg_mul_norm_add_sq_le
-- name    : GlobalTheory.exp_neg_mul_norm_add_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:37.0314+00:00
-- url     : https://prove2.me/theorems/5529b5a1-b936-4a3b-bb8a-5d7aab643e0b
-- title:
--   Global Theory: exp neg mul norm add sq le
-- statement:
--   The Global Theory construction uses the exp neg mul norm add sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L34-L43

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L]
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.exp_neg_mul_norm_add_sq_le {a R : ℝ} (ha : 0 ≤ a) (x : E) {u : E} (hu : ‖u‖ ≤ R) :
    Real.exp (-a * ‖x + u‖ ^ 2) ≤ Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by sorry
