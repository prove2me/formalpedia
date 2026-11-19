-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialUniformBoundPublic
-- name    : Kyprianou.Ch01.brownianUpperStoppedExponentialUniformBoundPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:22:23.676474+00:00
-- url     : https://prove2.me/theorems/1bef0441-a715-46ea-9ad7-1061154e1312
-- title:
--   Brownian upper passage: common integrable bound for capped stopped exponentials
-- statement:
--   For a.e. continuous Brownian path started at zero, the capped stopped first upper passage value is at or below the barrier. Since the adjustment root is nonnegative and the discount is positive, every stopped exponential has absolute value bounded by exp(theta*x), uniformly in the horizon N. This supplies the integrable constant required for dominated convergence.
-- source:
--   Kyprianou (2006), Exercise 1.10(ii) worked solution, printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperStoppedExponentialUniformBoundPublic
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
    ∀ᵐ ω ∂P, ∀ N : ℕ,
      ‖F N ω‖ ≤ Real.exp (theta * x) := by sorry
