-- Prove2me | Theorems.Thm_GlobalTheory_coveringRadius_and_closest_point
-- name    : GlobalTheory.coveringRadius_and_closest_point
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:01.071499+00:00
-- url     : https://prove2.me/theorems/f2b2413e-a612-4dfc-a1a7-4e2993d0ca76
-- title:
--   Global Theory: covering Radius and closest point
-- statement:
--   The Global Theory construction uses the covering Radius and closest point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L204-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/AbsTwoMulInnerLeOfNormSubEqInfDist.lean#L204-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {L : Submodule ℤ E}

theorem GlobalTheory.coveringRadius_and_closest_point [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    (∀ (v : Fin (finrank ℝ E) → E) (r : ℝ), LinearIndependent ℝ v → (∀ i, v i ∈ L) →
      (∀ i, ‖v i‖ ≤ r) → ∀ x : E, ∃ w ∈ L, ‖x - w‖ ≤ √(finrank ℝ E) / 2 * r) ∧
    coveringRadius L ≤ √(finrank ℝ E) / 2 * lastMin L ∧
    (∀ x : E, ∃ w ∈ L, ∀ z ∈ L, ‖x - w‖ ≤ ‖x - z‖) ∧
    (∀ p : E, ∀ w ∈ L, (∀ z ∈ L, ‖p - w‖ ≤ ‖p - z‖) →
      ∀ y ∈ L, |2 * ⟪p - w, y⟫_ℝ| ≤ ‖y‖ ^ 2) := by sorry
