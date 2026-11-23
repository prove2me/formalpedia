-- Prove2me | Theorems.Thm_GlobalTheory_poisson_gaussian_lattice_cos
-- name    : GlobalTheory.poisson_gaussian_lattice_cos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:54.816498+00:00
-- url     : https://prove2.me/theorems/3e77d80e-69d6-474c-88d0-f6b6d9bd7e96
-- title:
--   Global Theory: poisson gaussian lattice cos
-- statement:
--   The Global Theory construction uses the poisson gaussian lattice cos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L275-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L275-L293

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

theorem GlobalTheory.poisson_gaussian_lattice_cos {t : ℝ} (ht : 0 < t) (u : E) :
    (Summable fun y : dualLattice L ↦
      Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫)) ∧
    ∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) =
      (ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) *
        ∑' y : dualLattice L,
          Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * ⟪(y : E), u⟫) := by sorry
