-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Slice_card_stabilizer_subgroup
-- name    : GlobalTheory.Mass.Slice.card_stabilizer_subgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:56.959268+00:00
-- url     : https://prove2.me/theorems/f9a72586-a1a4-5f73-8fd3-5427ad3a7924
-- title:
--   Slice: card stabilizer subgroup
-- statement:
--   The Slice construction uses the card stabilizer subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumRestrictSlice.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumRestrictSlice.lean#L21-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumRestrictSlice
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Slice

theorem GlobalTheory.Mass.Slice.card_stabilizer_subgroup {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) := by sorry
