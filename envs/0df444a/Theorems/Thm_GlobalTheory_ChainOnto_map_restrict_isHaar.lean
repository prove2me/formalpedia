-- Prove2me | Theorems.Thm_GlobalTheory_ChainOnto_map_restrict_isHaar
-- name    : GlobalTheory.ChainOnto.map_restrict_isHaar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:04.772623+00:00
-- url     : https://prove2.me/theorems/e4e5a262-441d-42f1-9f3a-f8a190f711b6
-- title:
--   Chain Onto: map restrict is Haar
-- statement:
--   The Chain Onto construction uses the map restrict is Haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MapRestrictIsHaarOfOpenProductCompact.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MapRestrictIsHaarOfOpenProductCompact.lean#L6-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.map_restrict_isHaar : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by sorry
