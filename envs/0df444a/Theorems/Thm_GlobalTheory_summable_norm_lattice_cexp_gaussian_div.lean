-- Prove2me | Theorems.Thm_GlobalTheory_summable_norm_lattice_cexp_gaussian_div
-- name    : GlobalTheory.summable_norm_lattice_cexp_gaussian_div
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:40.160731+00:00
-- url     : https://prove2.me/theorems/b19f217c-a878-4dd5-a3d8-b3abcc7ed4df
-- title:
--   Global Theory: summable norm lattice cexp gaussian div
-- statement:
--   The Global Theory construction uses the summable norm lattice cexp gaussian div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L212-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L212-L218

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

theorem GlobalTheory.summable_norm_lattice_cexp_gaussian_div {b : ℂ} (hb : 0 < b.re) (w : E) :
    Summable fun y : L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b)‖ := by sorry
