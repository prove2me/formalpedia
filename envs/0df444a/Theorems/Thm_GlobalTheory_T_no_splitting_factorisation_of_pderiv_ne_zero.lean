-- Prove2me | Theorems.Thm_GlobalTheory_T_no_splitting_factorisation_of_pderiv_ne_zero
-- name    : GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:54.837803+00:00
-- url     : https://prove2.me/theorems/d0dbf30b-c07f-48ef-ac9c-55bd2ee6d6c5
-- title:
--   T: no splitting factorisation of pderiv ne zero
-- statement:
--   The T construction uses the no splitting factorisation of pderiv ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoSplittingFactorisationOfPderivNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoSplittingFactorisationOfPderivNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoSplittingFactorisationOfPderivNeZeroStatement
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

theorem GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero : ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ), (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by sorry
