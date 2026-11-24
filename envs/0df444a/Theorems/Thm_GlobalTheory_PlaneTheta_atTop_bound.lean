-- Prove2me | Theorems.Thm_GlobalTheory_PlaneTheta_atTop_bound
-- name    : GlobalTheory.PlaneTheta.atTop_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:17.142231+00:00
-- url     : https://prove2.me/theorems/66e2d0cc-e861-4d62-b114-e3d744365d85
-- title:
--   Plane Theta: at Top bound
-- statement:
--   The Plane Theta construction uses the at Top bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L47-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]

theorem GlobalTheory.PlaneTheta.atTop_bound (u : E) (hu : ∀ x : L, (x : E) + u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      =O[atTop] (fun t => Real.exp (-c * t)) := by sorry
