-- Prove2me | Theorems.Thm_GlobalTheory_exists_linearEquiv_of_irreducible_isHW
-- name    : GlobalTheory.exists_linearEquiv_of_irreducible_isHW
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:28.379228+00:00
-- url     : https://prove2.me/theorems/5cd2dbc9-26b3-4583-bbcd-ee1cb87abb11
-- title:
--   Global Theory: exists linear Equiv of irreducible is HW
-- statement:
--   The Global Theory construction uses the exists linear Equiv of irreducible is HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLinearEquivOfIrreducibleIsHW.lean#L62-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLinearEquivOfIrreducibleIsHW.lean#L62-L92

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsStableSubmoduleTopWeightLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLinearEquivOfIrreducibleIsHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory

theorem GlobalTheory.exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by sorry
