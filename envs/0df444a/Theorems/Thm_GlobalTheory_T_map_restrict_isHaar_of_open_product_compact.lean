-- Prove2me | Theorems.Thm_GlobalTheory_T_map_restrict_isHaar_of_open_product_compact
-- name    : GlobalTheory.T.map_restrict_isHaar_of_open_product_compact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:31.932157+00:00
-- url     : https://prove2.me/theorems/eb603cdd-874b-4303-9de3-f064853b9161
-- title:
--   T: map restrict is Haar of open product compact
-- statement:
--   The T construction uses the map restrict is Haar of open product compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MapRestrictIsHaarOfOpenProductCompactStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MapRestrictIsHaarOfOpenProductCompactStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.map_restrict_isHaar_of_open_product_compact : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by sorry
