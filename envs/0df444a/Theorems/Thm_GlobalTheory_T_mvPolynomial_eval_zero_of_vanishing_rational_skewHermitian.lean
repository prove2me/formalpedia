-- Prove2me | Theorems.Thm_GlobalTheory_T_mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian
-- name    : GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:43.917355+00:00
-- url     : https://prove2.me/theorems/80f5a54c-bbdd-4000-b5f1-c037f23969c1
-- title:
--   T: mv Polynomial eval zero of vanishing rational skew Hermitian
-- statement:
--   The T construction uses the mv Polynomial eval zero of vanishing rational skew Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → MvPolynomial.eval (upt (ratPt S)) Q = 0) → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) → MvPolynomial.eval (upt Y) Q = 0 := by sorry
