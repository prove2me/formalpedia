-- Prove2me | Theorems.Thm_GlobalTheory_LocalCoord_exists_local_coordinates
-- name    : GlobalTheory.LocalCoord.exists_local_coordinates
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:01.588679+00:00
-- url     : https://prove2.me/theorems/b3372805-9e7c-4303-86ca-d3fd00a001b0
-- title:
--   Local Coord: exists local coordinates
-- statement:
--   The Local Coord construction uses the exists local coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalCoordinates.lean#L94-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalCoordinates.lean#L94-L231

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LocalCoord

theorem GlobalTheory.LocalCoord.exists_local_coordinates :
    ∀ (k A K B : Type) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] (φ : TensorProduct k K A →ₐ[K] B) (χ : B →ₐ[K] K) (g : ℕ) (m : Ideal A), Function.Surjective φ → RingHom.ker φ ≤ nilradical _ → (∀ a : A, a ∈ m ↔ χ (φ (1 ⊗ₜ a)) = 0) → m.IsMaximal → (∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧ ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t)) → IsReduced B → ∃ (u : Fin g → A) (s : A), s ∉ m ∧ (∀ i, u i ∈ m) ∧ ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔ nilradical A := by sorry
