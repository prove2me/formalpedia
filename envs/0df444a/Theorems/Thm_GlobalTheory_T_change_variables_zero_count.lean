-- Prove2me | Theorems.Thm_GlobalTheory_T_change_variables_zero_count
-- name    : GlobalTheory.T.change_variables_zero_count
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:30:39.01094+00:00
-- url     : https://prove2.me/theorems/38250f83-c1a6-4571-8311-0ba9682ce38e
-- title:
--   T: change variables zero count
-- statement:
--   The T construction uses the change variables zero count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCountStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCountStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
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

theorem GlobalTheory.T.change_variables_zero_count : ∀ (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ) (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → A ⊆ U → MeasurableSet A → Measurable h → ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) = ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) * ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by sorry
