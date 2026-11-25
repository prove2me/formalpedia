-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_valuation_map_uniformiser
-- name    : GlobalTheory.adicCompletion_valuation_map_uniformiser
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:02:30.857552+00:00
-- url     : https://prove2.me/theorems/21399d21-6d83-4ba5-89bd-410dfa731358
-- title:
--   Global Theory: adic Completion valuation map uniformiser
-- statement:
--   The Global Theory construction uses the adic Completion valuation map uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdicCompletionValuationMapUniformiser.lean#L6-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdicCompletionValuationMapUniformiser.lean#L6-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.adicCompletion_valuation_map_uniformiser : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by sorry
