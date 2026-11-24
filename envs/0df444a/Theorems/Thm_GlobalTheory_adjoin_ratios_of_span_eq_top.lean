-- Prove2me | Theorems.Thm_GlobalTheory_adjoin_ratios_of_span_eq_top
-- name    : GlobalTheory.adjoin_ratios_of_span_eq_top
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:41.432503+00:00
-- url     : https://prove2.me/theorems/25b89fb0-db55-422f-aaf7-da2da4f0f5aa
-- title:
--   Global Theory: adjoin ratios of span eq top
-- statement:
--   The Global Theory construction uses the adjoin ratios of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AdjoinRatiosOfSpanEqTop.lean#L5-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AdjoinRatiosOfSpanEqTop.lean#L5-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AdjoinRatiosOfSpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.adjoin_ratios_of_span_eq_top :
    ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) (m : ℕ) (w : Fin m → R) (k : Fin m), Ideal.span (Set.range w) = ⊤ → (w k : Ω) ≠ 0 → ∀ R' : Subalgebra K Ω, R' = Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => (w i : Ω) / (w k : Ω)) → ∃ h : R ≤ R', (w k : Ω)⁻¹ ∈ R' ∧ (Algebra.Smooth K R → Algebra.Smooth K R') ∧ ∀ (L : Type) [Field L] [Algebra K L] (ψ : R →ₐ[K] L), ψ (w k) ≠ 0 → ∃ ψ' : R' →ₐ[K] L, ψ'.comp (Subalgebra.inclusion h) = ψ ∧ ∀ i (hi : (w i : Ω) / (w k : Ω) ∈ R'), ψ' ⟨_, hi⟩ = ψ (w i) / ψ (w k) := by sorry
