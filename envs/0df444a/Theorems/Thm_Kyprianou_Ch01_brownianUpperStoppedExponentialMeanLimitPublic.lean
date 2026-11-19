-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialMeanLimitPublic
-- name    : Kyprianou.Ch01.brownianUpperStoppedExponentialMeanLimitPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:13:46.993212+00:00
-- url     : https://prove2.me/theorems/809402bd-d960-4497-88ae-b7fb0f136972
-- title:
--   Brownian upper passage: bounded stopped exponential converges in expected value
-- statement:
--   As the finite stopping horizon increases over positive integers, the expected bounded stopped Brownian adjustment-root exponential converges to exp(theta x) times the Laplace transform of strict first upper passage, with the infinite-passage convention zero. This requires contact at first crossing, exponential decay on non-crossing paths, integrable domination, and convergence under the integral.
-- source:
--   Kyprianou (2006), solution to Exercise 1.10(ii), printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperStoppedExponentialMeanLimitPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let F : ℕ → Ω → ℝ := fun N ω =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ))
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    Tendsto (fun N : ℕ => ∫ ω, F N ω ∂P)
      atTop (nhds (Real.exp (theta * x) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P))) := by sorry
