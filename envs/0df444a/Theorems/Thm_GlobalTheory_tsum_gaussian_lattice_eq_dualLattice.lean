-- Prove2me | Theorems.Thm_GlobalTheory_tsum_gaussian_lattice_eq_dualLattice
-- name    : GlobalTheory.tsum_gaussian_lattice_eq_dualLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:54.833874+00:00
-- url     : https://prove2.me/theorems/b62df0f1-58b5-45e6-ac8b-7ce41feb84b3
-- title:
--   Global Theory: tsum gaussian lattice eq dual Lattice
-- statement:
--   The Global Theory construction uses the tsum gaussian lattice eq dual Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L295-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L295-L300

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

theorem GlobalTheory.tsum_gaussian_lattice_eq_dualLattice {t : ℝ} (ht : 0 < t) :
    ∑' x : L, Real.exp (-π * t * ‖(x : E)‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L, Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by sorry
