-- Prove2me | Theorems.Thm_GlobalTheory_BaseChangeComponents_components
-- name    : GlobalTheory.BaseChangeComponents.components
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:38.494257+00:00
-- url     : https://prove2.me/theorems/43c38fe2-9fed-454f-acb4-a34ff0c10913
-- title:
--   Base Change Components: components
-- statement:
--   The Base Change Components construction uses the components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L199-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IsNoetherianRingTensor.lean#L199-L218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

theorem GlobalTheory.BaseChangeComponents.components : ∀ (K F Ω : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω] (R₀ : Subalgebra K Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∃ (J : Type) (_ : Finite J) (Ω' : J → Type) (_ : ∀ j, Field (Ω' j)) (α : ∀ j, Ω →+* Ω' j) (γ : ∀ j, F →+* Ω' j), (∀ j (a : K), α j (algebraMap K Ω a) = γ j (algebraMap K F a)) ∧ (∀ j, Subfield.closure (Set.range (α j) ∪ Set.range (γ j)) = ⊤) ∧ ∀ (R : Subalgebra K Ω), Algebra.Smooth K R → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) → (∀ j, IsIntegrallyClosed (Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)))) ∧ ∀ (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L), (∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) → ∃ (j : J) (φ : Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)) →+* L), (∀ (r : R) (h : α j r ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨α j r, h⟩ = ψ r) ∧ ∀ (a : F) (h : γ j a ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨γ j a, h⟩ = χ a := by sorry
