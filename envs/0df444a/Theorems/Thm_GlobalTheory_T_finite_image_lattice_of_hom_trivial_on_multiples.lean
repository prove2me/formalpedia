-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_image_lattice_of_hom_trivial_on_multiples
-- name    : GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:20.349746+00:00
-- url     : https://prove2.me/theorems/0632f5c5-48e9-5ac4-9393-5f36de63bb24
-- title:
--   T: finite image lattice of hom trivial on multiples
-- statement:
--   The T construction uses the finite image lattice of hom trivial on multiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeHomFiniteImageOfTrivialOnMultiplesStatement.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeHomFiniteImageOfTrivialOnMultiplesStatement.lean#L10-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiples
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeHomFiniteImageOfTrivialOnMultiplesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (G : Type) [Group G] (e : (Fin g → ℂ) → G) (N : ℕ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z w, e (z + w) = e z * e w) → 0 < N →
    (∀ l ∈ Λ, e ((N : ℂ) • l) = 1) → (e '' (Λ : Set (Fin g → ℂ))).Finite := by sorry
