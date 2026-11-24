-- Prove2me | Theorems.Thm_GlobalTheory_lattice_hom_finite_image_of_trivial_on_multiples
-- name    : GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:20.197075+00:00
-- url     : https://prove2.me/theorems/116add98-6a1b-4142-afdb-5991c65e5138
-- title:
--   Global Theory: lattice hom finite image of trivial on multiples
-- statement:
--   The Global Theory construction uses the lattice hom finite image of trivial on multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeHomFiniteImageOfTrivialOnMultiples.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeHomFiniteImageOfTrivialOnMultiples.lean#L9-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiples
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
open GlobalTheory

theorem GlobalTheory.lattice_hom_finite_image_of_trivial_on_multiples :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by sorry
