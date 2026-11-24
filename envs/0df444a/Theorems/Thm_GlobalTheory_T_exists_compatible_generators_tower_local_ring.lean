-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_compatible_generators_tower_local_ring
-- name    : GlobalTheory.T.exists_compatible_generators_tower_local_ring
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:41.237702+00:00
-- url     : https://prove2.me/theorems/26b5eaf0-827e-4c3b-9764-301f340a81f5
-- title:
--   T: exists compatible generators tower local ring
-- statement:
--   The T construction uses the exists compatible generators tower local ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleGeneratorsTowerLocalRingStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCompatibleGeneratorsTowerLocalRingStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleGeneratorsTowerLocalRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleGeneratorsTowerLocalRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_compatible_generators_tower_local_ring : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by sorry
