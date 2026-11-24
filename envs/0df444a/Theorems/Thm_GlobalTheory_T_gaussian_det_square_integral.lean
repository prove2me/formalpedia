-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussian_det_square_integral
-- name    : GlobalTheory.T.gaussian_det_square_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:40:50.385596+00:00
-- url     : https://prove2.me/theorems/d1465810-17e8-4305-ac6b-9e0c87fdc3cb
-- title:
--   T: gaussian det square integral
-- statement:
--   The T construction uses the gaussian det square integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegralStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegralStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
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

theorem GlobalTheory.T.gaussian_det_square_integral : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (G : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (G.conjTranspose * G).det.re) := by sorry
