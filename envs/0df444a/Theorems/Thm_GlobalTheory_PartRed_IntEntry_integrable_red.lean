-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_integrable_red
-- name    : GlobalTheory.PartRed.IntEntry.integrable_red
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:55.802839+00:00
-- url     : https://prove2.me/theorems/78794655-0865-41c5-bde1-9b17bd242a59
-- title:
--   Int Entry: integrable red
-- statement:
--   The Int Entry construction uses the integrable red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L68-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L68-L96

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

theorem GlobalTheory.PartRed.IntEntry.integrable_red : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ x : Matrix R Q k, Integrable (fun y : I → k => Φ (fillAt β E I x y) * (ψ (-w (fillAt β E I x y)) : ℂ)) (Measure.pi fun _ => ν) := by sorry
