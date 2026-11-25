-- Prove2me | Theorems.Thm_GlobalTheory_poisson_gaussian_lattice
-- name    : GlobalTheory.poisson_gaussian_lattice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:45.170644+00:00
-- url     : https://prove2.me/theorems/8a584ff0-83e4-4b67-99c5-211cde30014b
-- title:
--   Global Theory: poisson gaussian lattice
-- statement:
--   The Global Theory construction uses the poisson gaussian lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L248-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L248-L265

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

theorem GlobalTheory.poisson_gaussian_lattice {t : ℝ} (ht : 0 < t) (u : E) :
    (Summable fun x : L ↦ Real.exp (-π * t * ‖(x : E) + u‖ ^ 2)) ∧
    (Summable fun y : dualLattice L ↦ ‖(Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ((∑' x : L, Real.exp (-π * t * ‖(x : E) + u‖ ^ 2) : ℝ) : ℂ) =
      (((ZLattice.covolume L)⁻¹ * t ^ (-(finrank ℝ E / 2 : ℝ)) : ℝ) : ℂ) *
        ∑' y : dualLattice L, (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) : ℂ) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by sorry
