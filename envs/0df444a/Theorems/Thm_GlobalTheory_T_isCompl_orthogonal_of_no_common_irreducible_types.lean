-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompl_orthogonal_of_no_common_irreducible_types
-- name    : GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:57.992968+00:00
-- url     : https://prove2.me/theorems/b0bb16ab-8464-4785-a887-a578e5f85cea
-- title:
--   T: is Compl orthogonal of no common irreducible types
-- statement:
--   The T construction uses the is Compl orthogonal of no common irreducible types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypesStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsComplOrthogonalOfNoCommonIrreducibleTypesStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsComplOrthogonalOfNoCommonIrreducibleTypes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsComplOrthogonalOfNoCommonIrreducibleTypesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by sorry
