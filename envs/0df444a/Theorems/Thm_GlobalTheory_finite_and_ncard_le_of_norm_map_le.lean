-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_norm_map_le
-- name    : GlobalTheory.finite_and_ncard_le_of_norm_map_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:19.028269+00:00
-- url     : https://prove2.me/theorems/1d885e05-51ac-4da5-a373-e82ffdb47f9b
-- title:
--   Global Theory: finite and ncard le of norm map le
-- statement:
--   The Global Theory construction uses the finite and ncard le of norm map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L281-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L281-L293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GlobalTheory.finite_and_ncard_le_of_norm_map_le (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G)
    (hG : ∀ g ∈ G, ∀ x : L, ‖(φ g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by sorry
