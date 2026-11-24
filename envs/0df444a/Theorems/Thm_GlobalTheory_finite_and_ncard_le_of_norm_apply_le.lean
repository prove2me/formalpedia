-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_norm_apply_le
-- name    : GlobalTheory.finite_and_ncard_le_of_norm_apply_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:24.687939+00:00
-- url     : https://prove2.me/theorems/0c4c7f59-018f-498a-841c-d016bd2f8942
-- title:
--   Global Theory: finite and ncard le of norm apply le
-- statement:
--   The Global Theory construction uses the finite and ncard le of norm apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L260-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L260-L279

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

theorem GlobalTheory.finite_and_ncard_le_of_norm_apply_le (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {d R : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hL : ∀ x ∈ L, x ≠ 0 → d ≤ ‖x‖) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G) (hG : ∀ g ∈ G, ∀ i, ‖(φ g (v i) : E)‖ ≤ R) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * R / d) ^ (n ^ 2) := by sorry
