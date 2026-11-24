-- Prove2me | Theorems.Thm_GlobalTheory_FactorwiseExtension_invariant_insert
-- name    : GlobalTheory.FactorwiseExtension.invariant_insert
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:49.356652+00:00
-- url     : https://prove2.me/theorems/80b8ca74-cc52-4b57-8c11-779d54ce3172
-- title:
--   Factorwise Extension: invariant insert
-- statement:
--   The Factorwise Extension construction uses the invariant insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L53-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L53-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]

theorem GlobalTheory.FactorwiseExtension.invariant_insert (A B : ∀ τ, Submodule ℂ (H τ)) (hAB : ∀ τ, A τ ≤ B τ)
    (Rk Rg : ∀ τ, Set ((H τ → H τ) × (E →ₗ[ℂ] E)))
    (hRk : ∀ τ, ∀ r ∈ Rk τ, ∀ x ∈ A τ, r.1 x ∈ A τ) (hRg : ∀ τ, ∀ r ∈ Rg τ, ∀ x ∈ B τ, r.1 x ∈ B τ)
    (C : ∀ τ, Submodule ℂ (H τ →ₗ[ℂ] E))
    (hC : ∀ τ, ∀ L ∈ C τ, ∀ L' : H τ →ₗ[ℂ] E, (∀ x ∈ B τ, L' x = L x) → L' ∈ C τ)
    (hext : ∀ τ (L : H τ →ₗ[ℂ] E), (∀ r ∈ Rk τ, ∀ x ∈ A τ, L (r.1 x) = r.2 (L x)) →
      ∃ L' ∈ C τ, (∀ r ∈ Rg τ, ∀ x ∈ B τ, L' (r.1 x) = r.2 (L' x)) ∧ ∀ x ∈ A τ, L' x = L x)
    (huniq : ∀ τ, ∀ L ∈ C τ, (∀ x ∈ A τ, L x = 0) → ∀ x ∈ B τ, L x = 0)
    (hpostC : ∀ τ τ', τ ≠ τ' → ∀ r ∈ Rk τ ∪ Rg τ, ∀ L ∈ C τ', r.2 ∘ₗ L ∈ C τ')
    (hbs : ∀ τ τ', τ ≠ τ' → ∀ F : H τ →ₗ[ℂ] H τ' →ₗ[ℂ] E, (∀ w ∈ B τ, F w ∈ C τ') →
      (∀ a ∈ A τ', F.flip a ∈ C τ) → ∀ b ∈ B τ', F.flip b ∈ C τ)
    (T₀ : MultilinearMap ℂ H E) (s : Finset ι) (τ₀ : ι) (hτ₀ : τ₀ ∉ s) (T : MultilinearMap ℂ H E)
    (hT : Invariant A B Rk Rg C T₀ s T) : ∃ T', Invariant A B Rk Rg C T₀ (insert τ₀ s) T' := by sorry
