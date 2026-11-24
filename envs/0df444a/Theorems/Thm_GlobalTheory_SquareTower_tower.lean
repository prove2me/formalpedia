-- Prove2me | Theorems.Thm_GlobalTheory_SquareTower_tower
-- name    : GlobalTheory.SquareTower.tower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:22:26.108013+00:00
-- url     : https://prove2.me/theorems/5a1547bc-3620-47e9-af3f-00bf4865a13e
-- title:
--   Square Tower: tower
-- statement:
--   The Square Tower construction uses the tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquarePresentationOfTower.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquarePresentationOfTower.lean#L46-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SquareTower
open MvPolynomial

theorem GlobalTheory.SquareTower.tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by sorry
