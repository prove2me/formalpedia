-- Prove2me | Theorems.Thm_GlobalTheory_Mass_orbSum_eq_sum_reps
-- name    : GlobalTheory.Mass.orbSum_eq_sum_reps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:41.786681+00:00
-- url     : https://prove2.me/theorems/b51e4bfd-f175-42c7-a4df-4fe3912b0b2d
-- title:
--   Mass: orb Sum eq sum reps
-- statement:
--   The Mass construction uses the orb Sum eq sum reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumEqSumOrbitReps.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumEqSumOrbitReps.lean#L12-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass
open NumberField Matrix
open scoped ENNReal Classical

theorem GlobalTheory.Mass.orbSum_eq_sum_reps : ∀ (G α : Type) [Group G] [MulAction G α]
    (X : Set α) (N : α → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → (∀ (g : G) x, N (g • x) = N x) →
    ∀ s : Finset α, (∀ x ∈ s, x ∈ X) → (∀ x ∈ X, ∃! y, y ∈ s ∧ ∃ g : G, g • y = x) →
    _root_.GlobalTheory.Mass.orbSum G X N =
      ∑ x ∈ s, ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by sorry
