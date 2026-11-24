-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LagFun_exists_invariant_form
-- name    : GlobalTheory.CompanionTheory.LagFun.exists_invariant_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:23:45.735275+00:00
-- url     : https://prove2.me/theorems/1ef06a03-6027-431a-9663-645cdcbb0816
-- title:
--   Lag Fun: exists invariant form
-- statement:
--   The Lag Fun construction uses the exists invariant form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsInvariantForm.lean#L26-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsInvariantForm.lean#L26-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LagFun

theorem GlobalTheory.CompanionTheory.LagFun.exists_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 → ∀ large₂ : Submodule k ((κ → k) × (κ → k)), (∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by sorry
