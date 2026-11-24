-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_IntEntry_red_insert
-- name    : GlobalTheory.PartRed.IntEntry.red_insert
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:52.118523+00:00
-- url     : https://prove2.me/theorems/39a6d2a3-1d9c-44c7-8ef9-aaa17304fbd4
-- title:
--   Int Entry: red insert
-- statement:
--   The Int Entry construction uses the red insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L98-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionIntegrateEntryOfTranslation.lean#L98-L127

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

theorem GlobalTheory.PartRed.IntEntry.red_insert : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → e ∉ I → ∀ (Φ : Matrix R Q k → ℂ) (x : Matrix R Q k), Integrable (fun y : ↥(insert e I : Finset (R × Q)) → k => Φ (fillAt β E (insert e I) x y) * (ψ (-w (fillAt β E (insert e I) x y)) : ℂ)) (Measure.pi fun _ => ν) → red ψ ν w β E (insert e I) Φ x = ∫ s, red ψ ν w β E I Φ (x + Matrix.single e.1 e.2 (s - x e.1 e.2)) ∂ν := by sorry
