-- Prove2me | Theorems.Thm_GlobalTheory_T_orbitWeightedStabilizerSum_transport_equivariant
-- name    : GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:41.901811+00:00
-- url     : https://prove2.me/theorems/74acea88-8da3-59da-9079-c3709c098c12
-- title:
--   T: orbit Weighted Stabilizer Sum transport equivariant
-- statement:
--   The T construction uses the orbit Weighted Stabilizer Sum transport equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumTransportEquivariantStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumTransportEquivariantStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariantStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), Stable G X → Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → orbSum G X (fun x => N (f x)) = orbSum G' Y N := by sorry
