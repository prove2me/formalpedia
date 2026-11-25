-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finiteDimensional_orbit_of_boundedRank_generated
-- name    : GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:56.69571+00:00
-- url     : https://prove2.me/theorems/e492a290-cfe0-5d2f-afbe-0950df86365b
-- title:
--   T: exists finite Dimensional orbit of bounded Rank generated
-- statement:
--   The T construction uses the exists finite Dimensional orbit of bounded Rank generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement.lean#L6-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFiniteDimensionalOrbitOfBoundedRankGenerat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated : ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by sorry
