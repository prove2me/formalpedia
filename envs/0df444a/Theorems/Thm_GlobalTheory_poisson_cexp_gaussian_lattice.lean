-- Prove2me | Theorems.Thm_GlobalTheory_poisson_cexp_gaussian_lattice
-- name    : GlobalTheory.poisson_cexp_gaussian_lattice
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:56.030942+00:00
-- url     : https://prove2.me/theorems/e8afbac2-d5a7-49de-8af5-a892ac070803
-- title:
--   Global Theory: poisson cexp gaussian lattice
-- statement:
--   The Global Theory construction uses the poisson cexp gaussian lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L220-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L220-L246

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

theorem GlobalTheory.poisson_cexp_gaussian_lattice {b : ℂ} (hb : 0 < b.re) (w u : E) :
    (Summable fun x : L ↦ ‖Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 +
      2 * π * Complex.I * ⟪w, (x : E) + u⟫)‖) ∧
    (Summable fun y : dualLattice L ↦ ‖Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
      Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫)‖) ∧
    ∑' x : L, Complex.exp (-π * b * ‖(x : E) + u‖ ^ 2 + 2 * π * Complex.I * ⟪w, (x : E) + u⟫) =
      (ZLattice.covolume L : ℂ)⁻¹ * b ^ (-(finrank ℝ E / 2 : ℂ)) *
        ∑' y : dualLattice L, Complex.exp (-π * ‖(y : E) - w‖ ^ 2 / b) *
          Complex.exp (2 * π * Complex.I * ⟪(y : E), u⟫) := by sorry
