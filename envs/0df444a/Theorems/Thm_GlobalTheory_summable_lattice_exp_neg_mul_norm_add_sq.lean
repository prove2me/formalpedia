-- Prove2me | Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_mul_norm_add_sq
-- name    : GlobalTheory.summable_lattice_exp_neg_mul_norm_add_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:38.364386+00:00
-- url     : https://prove2.me/theorems/bf820ca6-9e96-4a22-9570-d0c375bb3629
-- title:
--   Global Theory: summable lattice exp neg mul norm add sq
-- statement:
--   The Global Theory construction uses the summable lattice exp neg mul norm add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L45-L49

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

theorem GlobalTheory.summable_lattice_exp_neg_mul_norm_add_sq {a : ℝ} (ha : 0 < a) (u : E) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E) + u‖ ^ 2) := by sorry
