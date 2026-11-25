-- Prove2me | Theorems.Thm_GlobalTheory_tsum_poisson_lattice
-- name    : GlobalTheory.tsum_poisson_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:43.240698+00:00
-- url     : https://prove2.me/theorems/dea113c8-d868-4f64-8066-bd4917a2ee4e
-- title:
--   Global Theory: tsum poisson lattice
-- statement:
--   The Global Theory construction uses the tsum poisson lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean#L160-L165

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

theorem GlobalTheory.tsum_poisson_lattice [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    ∑' x : L, f (x + u) =
      (ZLattice.covolume L)⁻¹ • ∑' y : dualLattice L, e[⟪(y : E), u⟫] • 𝓕 f y := by sorry
