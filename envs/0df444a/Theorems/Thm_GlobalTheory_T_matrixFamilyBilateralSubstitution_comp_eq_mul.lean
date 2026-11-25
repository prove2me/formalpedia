-- Prove2me | Theorems.Thm_GlobalTheory_T_matrixFamilyBilateralSubstitution_comp_eq_mul
-- name    : GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:09.506799+00:00
-- url     : https://prove2.me/theorems/ada797ef-beb3-532a-b886-5bb31ef550fa
-- title:
--   T: matrix Family Bilateral Substitution comp eq mul
-- statement:
--   The T construction uses the matrix Family Bilateral Substitution comp eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionCompEqMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MatrixFamilyBilateralSubstitutionCompEqMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by sorry
