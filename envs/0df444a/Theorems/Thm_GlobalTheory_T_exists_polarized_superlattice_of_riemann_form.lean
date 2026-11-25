-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_polarized_superlattice_of_riemann_form
-- name    : GlobalTheory.T.exists_polarized_superlattice_of_riemann_form
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:36.738205+00:00
-- url     : https://prove2.me/theorems/2f9553d8-46ce-40dc-9dda-605a5d175949
-- title:
--   T: exists polarized superlattice of riemann form
-- statement:
--   The T construction uses the exists polarized superlattice of riemann form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannFormStatement.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannFormStatement.lean#L13-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_polarized_superlattice_of_riemann_form : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by sorry
