-- Prove2me | Theorems.Thm_GlobalTheory_TypeComplement_exists_typeComplement
-- name    : GlobalTheory.TypeComplement.exists_typeComplement
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:16:34.190455+00:00
-- url     : https://prove2.me/theorems/4ef1c03e-76e0-4617-956e-04b91d08f21a
-- title:
--   Type Complement: exists type Complement
-- statement:
--   The Type Complement construction uses the exists type Complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L109-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsComplementWithoutCommonIrreducibleTypes.lean#L109-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsComplementWithoutCommonIrreducibleTypes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TypeComplement

theorem GlobalTheory.TypeComplement.exists_typeComplement : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by sorry
