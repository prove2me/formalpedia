-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_exists_subgroup
-- name    : GlobalTheory.PartRed.IntEntry.exists_subgroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:54.036031+00:00
-- url     : https://prove2.me/theorems/36270130-105b-4289-9d04-5098dec87ff5
-- title:
--   Int Entry: exists subgroup
-- statement:
--   The Int Entry construction uses the exists subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L129-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L129-L158

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

theorem GlobalTheory.PartRed.IntEntry.exists_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (e : R × Q) (c : k), ∃ U : AddSubgroup k, IsOpen (U : Set k) ∧ IsCompact (U : Set k) ∧ ∀ u ∈ U, ψ (u * c) = 1 ∧ ∀ t, Φ (t + Matrix.single e.1 e.2 u) = Φ t := by sorry
