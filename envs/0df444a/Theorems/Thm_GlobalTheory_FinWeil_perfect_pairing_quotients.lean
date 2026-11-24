-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_perfect_pairing_quotients
-- name    : GlobalTheory.FinWeil.perfect_pairing_quotients
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:57.245781+00:00
-- url     : https://prove2.me/theorems/d325e19d-18d4-4313-8f42-15d69c7c5a45
-- title:
--   Fin Weil: perfect pairing quotients
-- statement:
--   The Fin Weil construction uses the perfect pairing quotients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PerfectPairingQuotients.lean#L49-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PerfectPairingQuotients.lean#L49-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil

theorem GlobalTheory.FinWeil.perfect_pairing_quotients : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by sorry
