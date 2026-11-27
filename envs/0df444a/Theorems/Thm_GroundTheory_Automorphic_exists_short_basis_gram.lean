-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_short_basis_gram
-- name    : GroundTheory.Automorphic.exists_short_basis_gram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:53.688627+00:00
-- url     : https://prove2.me/theorems/76b7625d-f4b4-4d0c-a1a6-ed5c00623b5a
-- title:
--   Automorphic: exists short basis gram
-- statement:
--   The Automorphic construction uses the exists short basis gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/GramReduction.lean#L56-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/GramReduction.lean#L56-L121

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction
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
open Module Matrix Submodule
open scoped RealInnerProductSpace
variable {J : Type*} [Fintype J]

theorem GroundTheory.Automorphic.exists_short_basis_gram (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (L : AddSubgroup (J → ℝ)) (μ : ℝ)
    (hμ : 0 < μ) (hL : span ℝ (L : Set (J → ℝ)) = ⊤)
    (hD : span ℝ {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} = ⊤)
    (hmin : ∀ y : J → ℝ, (∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n) → y ≠ 0 →
      μ ^ 2 ≤ y ⬝ᵥ (G *ᵥ y)) :
    ∃ e : Fin (Fintype.card J) → (J → ℝ), LinearIndependent ℝ e ∧
      ∀ i, e i ∈ L ∧ e i ⬝ᵥ (G *ᵥ e i) ≤ shortBasisBound (Fintype.card J) μ ^ 2 := by sorry
