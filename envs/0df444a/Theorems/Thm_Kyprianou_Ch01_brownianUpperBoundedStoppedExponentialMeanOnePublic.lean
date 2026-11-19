-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianUpperBoundedStoppedExponentialMeanOnePublic
-- name    : Kyprianou.Ch01.brownianUpperBoundedStoppedExponentialMeanOnePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:14:00.374317+00:00
-- url     : https://prove2.me/theorems/e3d9a631-feba-42f6-9a22-7d28802cfa22
-- title:
--   Brownian upper passage: expectation one for bounded stopped exponential
-- statement:
--   For drifted Brownian motion, the positive adjustment-root exponential stopped at the minimum of strict first upper passage and any finite horizon is integrable with expected value one. This is the bounded-time optional-sampling identity of Exercise 1.10(ii). A proof requires justified finite-grid approximation and uniform integrability.
-- source:
--   Kyprianou (2006), solution to Exercise 1.10(ii), printed page 306.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianUpperBoundedStoppedExponentialMeanOnePublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    ∀ T : ℝ≥0,
      let tauT : Ω → ℝ≥0 := fun ω =>
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Integrable (fun ω => Real.exp
        (theta * X (tauT ω) ω - q * (tauT ω : ℝ))) P ∧
      (∫ ω, Real.exp
        (theta * X (tauT ω) ω - q * (tauT ω : ℝ)) ∂P) = 1 := by sorry
