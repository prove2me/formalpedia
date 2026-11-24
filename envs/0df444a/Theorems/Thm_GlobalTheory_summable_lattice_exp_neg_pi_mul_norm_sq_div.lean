-- Prove2me | Theorems.Thm_GlobalTheory_summable_lattice_exp_neg_pi_mul_norm_sq_div
-- name    : GlobalTheory.summable_lattice_exp_neg_pi_mul_norm_sq_div
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:17.357707+00:00
-- url     : https://prove2.me/theorems/0252a080-0c47-4c4d-a736-668a9ea06993
-- title:
--   Global Theory: summable lattice exp neg pi mul norm sq div
-- statement:
--   The Global Theory construction uses the summable lattice exp neg pi mul norm sq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L269-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L269-L273

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
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]

theorem GlobalTheory.summable_lattice_exp_neg_pi_mul_norm_sq_div {t : ℝ} (ht : 0 < t) :
    Summable fun y : L ↦ Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by sorry
