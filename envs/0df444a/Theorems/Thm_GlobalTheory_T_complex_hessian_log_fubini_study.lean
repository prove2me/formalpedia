-- Prove2me | Theorems.Thm_GlobalTheory_T_complex_hessian_log_fubini_study
-- name    : GlobalTheory.T.complex_hessian_log_fubini_study
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:47:06.925125+00:00
-- url     : https://prove2.me/theorems/d63bfeca-f196-4bf6-a4a6-71a8bbfde9f8
-- title:
--   T: complex hessian log fubini study
-- statement:
--   The T construction uses the complex hessian log fubini study property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogFubiniStudyStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogFubiniStudyStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudy
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.complex_hessian_log_fubini_study : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by sorry
