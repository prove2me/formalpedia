-- Prove2me | Theorems.Thm_GlobalTheory_periodic_tsum_lattice_translate
-- name    : GlobalTheory.periodic_tsum_lattice_translate
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:09.818822+00:00
-- url     : https://prove2.me/theorems/b45592be-1a62-4854-9e3e-918af150cd08
-- title:
--   Global Theory: periodic tsum lattice translate
-- statement:
--   The Global Theory construction uses the periodic tsum lattice translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L76-L83

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
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

theorem GlobalTheory.periodic_tsum_lattice_translate (f : E → V) {z : E} (hz : z ∈ L) :
    Function.Periodic (fun u : E ↦ ∑' x : L, f (x + u)) z := by sorry
