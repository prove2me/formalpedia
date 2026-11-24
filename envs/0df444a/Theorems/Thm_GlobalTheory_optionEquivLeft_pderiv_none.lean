-- Prove2me | Theorems.Thm_GlobalTheory_optionEquivLeft_pderiv_none
-- name    : GlobalTheory.optionEquivLeft_pderiv_none
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:13.403053+00:00
-- url     : https://prove2.me/theorems/758957a8-5fe4-443d-b185-1d7a46e8030d
-- title:
--   Global Theory: option Equiv Left pderiv none
-- statement:
--   The Global Theory construction uses the option Equiv Left pderiv none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StandardEtaleMvPolynomialHypersurface.lean#L9-L18

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

theorem GlobalTheory.optionEquivLeft_pderiv_none (A : Type) [CommRing A] (n : ℕ)
    (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft A (Fin n) (pderiv none p) = Polynomial.derivative (optionEquivLeft A (Fin n) p) := by sorry
