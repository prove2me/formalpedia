-- Prove2me | Theorems.Thm_GlobalTheory_tsum_gaussian_lattice_add_le
-- name    : GlobalTheory.tsum_gaussian_lattice_add_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:32.064591+00:00
-- url     : https://prove2.me/theorems/5a925b61-91fc-46cf-aaa2-a20d953700dd
-- title:
--   Global Theory: tsum gaussian lattice add le
-- statement:
--   The Global Theory construction uses the tsum gaussian lattice add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L302-L310

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

theorem GlobalTheory.tsum_gaussian_lattice_add_le {t : ℝ} (ht : 0 < t) (u : E) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) ≤
      ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) := by sorry
