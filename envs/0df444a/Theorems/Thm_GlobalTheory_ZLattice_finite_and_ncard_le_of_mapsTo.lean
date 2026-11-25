-- Prove2me | Theorems.Thm_GlobalTheory_ZLattice_finite_and_ncard_le_of_mapsTo
-- name    : GlobalTheory.ZLattice_finite_and_ncard_le_of_mapsTo
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:02.307387+00:00
-- url     : https://prove2.me/theorems/48d602eb-5e8c-4e9a-a493-2a935a6b87c1
-- title:
--   Global Theory: ZLattice finite and ncard le of maps To
-- statement:
--   The Global Theory construction uses the ZLattice finite and ncard le of maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L319-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L319-L337

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

theorem GlobalTheory.ZLattice_finite_and_ncard_le_of_mapsTo [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : finrank ℝ E = n) {v : Fin n → E}
    (hvL : ∀ i, v i ∈ L) (hv : LinearIndependent ℝ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖v i‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → E →ₗ[ℝ] E) (hφ : Set.InjOn φ G) (hφL : ∀ g ∈ G, ∀ x ∈ L, φ g x ∈ L)
    (hG : ∀ g ∈ G, ∀ x ∈ L, ‖φ g x‖ ≤ c * ‖x‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by sorry
