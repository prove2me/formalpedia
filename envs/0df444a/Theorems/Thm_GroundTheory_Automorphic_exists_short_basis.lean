-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_short_basis
-- name    : GroundTheory.Automorphic.exists_short_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:01.920913+00:00
-- url     : https://prove2.me/theorems/1c1f4e83-cc75-4ce7-bf15-03230c3f8f1a
-- title:
--   Automorphic: exists short basis
-- statement:
--   The Automorphic construction uses the exists short basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Reduction.lean#L87-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Reduction.lean#L87-L359

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u

theorem GroundTheory.Automorphic.exists_short_basis (N : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X], finrank ℝ X = N → ∀ (L : AddSubgroup X) (μ : ℝ), 0 < μ →
    span ℝ (L : Set X) = ⊤ → span ℝ (latticeDual L : Set X) = ⊤ →
    (∀ y ∈ latticeDual L, y ≠ 0 → μ ≤ ‖y‖) →
    ∃ e : Fin N → X, LinearIndependent ℝ e ∧ ∀ i, e i ∈ L ∧ ‖e i‖ ≤ shortBasisBound N μ := by sorry
