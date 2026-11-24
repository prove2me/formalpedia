-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_presentation_square_at_point_of_localFactor
-- name    : GlobalTheory.T.exists_presentation_square_at_point_of_localFactor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:11.752893+00:00
-- url     : https://prove2.me/theorems/f10a8f45-a014-454c-a8ac-b682456289bf
-- title:
--   T: exists presentation square at point of local Factor
-- statement:
--   The T construction uses the exists presentation square at point of local Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPresentationSquareAtPointOfLocalFactorStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPresentationSquareAtPointOfLocalFactorStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactorStatement
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

theorem GlobalTheory.T.exists_presentation_square_at_point_of_localFactor : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by sorry
