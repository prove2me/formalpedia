-- Prove2me | Theorems.Thm_GlobalTheory_T_complex_hessian_log_dehomogenise
-- name    : GlobalTheory.T.complex_hessian_log_dehomogenise
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:33:36.19999+00:00
-- url     : https://prove2.me/theorems/90b7f465-2f14-4ad2-8edf-ac255ea3c5da
-- title:
--   T: complex hessian log dehomogenise
-- statement:
--   The T construction uses the complex hessian log dehomogenise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogDehomogeniseStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogDehomogeniseStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogenise
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
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

theorem GlobalTheory.T.complex_hessian_log_dehomogenise : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by sorry
