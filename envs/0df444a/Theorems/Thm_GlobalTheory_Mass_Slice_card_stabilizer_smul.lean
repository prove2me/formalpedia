-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Slice_card_stabilizer_smul
-- name    : GlobalTheory.Mass.Slice.card_stabilizer_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:48.47144+00:00
-- url     : https://prove2.me/theorems/f1a29527-4a93-458e-95aa-ecd1c6cad7c6
-- title:
--   Slice: card stabilizer smul
-- statement:
--   The Slice construction uses the card stabilizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumRestrictSlice.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitWeightedStabilizerSumRestrictSlice.lean#L15-L19

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

theorem GlobalTheory.Mass.Slice.card_stabilizer_smul (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by sorry
