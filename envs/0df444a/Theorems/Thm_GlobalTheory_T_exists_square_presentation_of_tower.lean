-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_square_presentation_of_tower
-- name    : GlobalTheory.T.exists_square_presentation_of_tower
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:17.670308+00:00
-- url     : https://prove2.me/theorems/d0d1b31f-1795-4e56-bf3b-17bdcfcf0983
-- title:
--   T: exists square presentation of tower
-- statement:
--   The T construction uses the exists square presentation of tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquarePresentationOfTowerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquarePresentationOfTowerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTowerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_square_presentation_of_tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by sorry
