-- Prove2me | Theorems.Thm_GlobalTheory_Mass_OrbTransport_main
-- name    : GlobalTheory.Mass.OrbTransport.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:22.518988+00:00
-- url     : https://prove2.me/theorems/88b2b472-16cd-5de8-ae25-f0901573e493
-- title:
--   Orb Transport: main
-- statement:
--   The Orb Transport construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumTransportEquivariant.lean#L28-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumTransportEquivariant.lean#L28-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbTransport
open NumberField Matrix
open scoped ENNReal Classical
open MulAction

theorem GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by sorry
