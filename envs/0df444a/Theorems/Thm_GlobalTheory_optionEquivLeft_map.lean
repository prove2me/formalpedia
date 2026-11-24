-- Prove2me | Theorems.Thm_GlobalTheory_optionEquivLeft_map
-- name    : GlobalTheory.optionEquivLeft_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:50.13164+00:00
-- url     : https://prove2.me/theorems/33d90d66-3192-4763-94fa-32d6ba6dfd29
-- title:
--   Global Theory: option Equiv Left map
-- statement:
--   The Global Theory construction uses the option Equiv Left map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface
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
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.optionEquivLeft_map (A : Type) [CommRing A] (n : ℕ) {k : Type} [Field k]
    (ψ : A →+* k) (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft k (Fin n) (map ψ p) = Polynomial.map (map ψ) (optionEquivLeft A (Fin n) p) := by sorry
