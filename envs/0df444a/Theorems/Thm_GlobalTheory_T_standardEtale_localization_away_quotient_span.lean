-- Prove2me | Theorems.Thm_GlobalTheory_T_standardEtale_localization_away_quotient_span
-- name    : GlobalTheory.T.standardEtale_localization_away_quotient_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:57.782802+00:00
-- url     : https://prove2.me/theorems/45e1b313-560e-499e-b5e5-0c2d2b641808
-- title:
--   T: standard Etale localization away quotient span
-- statement:
--   The T construction uses the standard Etale localization away quotient span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurfaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurfaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.standardEtale_localization_away_quotient_span : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by sorry
