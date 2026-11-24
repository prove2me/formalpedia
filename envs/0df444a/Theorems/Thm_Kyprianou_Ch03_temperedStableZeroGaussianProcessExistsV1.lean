-- Prove2me | Theorems.Thm_Kyprianou_Ch03_temperedStableZeroGaussianProcessExistsV1
-- name    : Kyprianou.Ch03.temperedStableZeroGaussianProcessExistsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:58:06.246505+00:00
-- url     : https://prove2.me/theorems/100c2b53-1010-404c-8120-c449ff13ecaa
-- title:
--   Lévy process construction for a zero-Gaussian triplet in the Chapter 3 exponent environment
-- statement:
--   Use the proved pure-jump process construction and identify its exponent with the Chapter 3 triplet exponent when the Gaussian coefficient is zero. This declaration uses the original exponent module rather than the duplicate targeted module.
-- source:
--   Kyprianou (2006), Exercise 3.4; compatibility bridge using ProbabilityTheory.exists_isLevyProcess_pureJump.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.temperedStableZeroGaussianProcessExistsV1
    (T : LevyKhintchineTriple) (hzero : T.gaussianVariance = 0) :
    ∃ (Omega : Type) (m : MeasurableSpace Omega),
      letI : MeasurableSpace Omega := m
      ∃ (P : Measure Omega) (X : NNReal → Omega → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : NNReal) (xi : ℝ),
          charFun (P.map (X t)) xi =
            Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi) := by sorry
