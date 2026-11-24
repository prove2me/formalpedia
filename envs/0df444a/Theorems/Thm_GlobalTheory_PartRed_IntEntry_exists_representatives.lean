-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_exists_representatives
-- name    : GlobalTheory.PartRed.IntEntry.exists_representatives
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:43.268879+00:00
-- url     : https://prove2.me/theorems/a7f67f30-2cf6-4125-b506-d4fd79681e9e
-- title:
--   Int Entry: exists representatives
-- statement:
--   The Int Entry construction uses the exists representatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L160-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L160-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry

theorem GlobalTheory.PartRed.IntEntry.exists_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ e : R × Q, ∃ S : Finset k, (∀ a ∈ S, ∀ b ∈ S, a - b ∈ U → a = b) ∧ ∀ t : Matrix R Q k, Φ t ≠ 0 → ∃ a ∈ S, t e.1 e.2 - a ∈ U := by sorry
