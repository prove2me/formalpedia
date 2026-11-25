-- Prove2me | Theorems.Thm_GlobalTheory_PlaneTheta_zero_bound
-- name    : GlobalTheory.PlaneTheta.zero_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:54.053704+00:00
-- url     : https://prove2.me/theorems/cd601386-0681-49ea-b551-d438c1e00955
-- title:
--   Plane Theta: zero bound
-- statement:
--   The Plane Theta construction uses the zero bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L63-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L63-L118

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

theorem GlobalTheory.PlaneTheta.zero_bound (hE : Module.finrank ℝ E = 2) (u : E) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => (∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      - 1 / (t * ZLattice.covolume L))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by sorry
