-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic
-- name    : GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:35.53512+00:00
-- url     : https://prove2.me/theorems/28e65378-2002-47fb-8ce7-7e43cfcdd461
-- title:
--   T: coeff matrix Family Bilateral Substitution monomial continuous algebraic
-- statement:
--   The T construction uses the coeff matrix Family Bilateral Substitution monomial continuous algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by sorry
