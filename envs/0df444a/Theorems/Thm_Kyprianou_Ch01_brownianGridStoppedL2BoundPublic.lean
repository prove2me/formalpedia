-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianGridStoppedL2BoundPublic
-- name    : Kyprianou.Ch01.brownianGridStoppedL2BoundPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:13:09.877777+00:00
-- url     : https://prove2.me/theorems/6fd0cb5a-ac38-436a-9ee2-0879553ec1df
-- title:
--   Public bounded-grid stopped Brownian adjustment exponential L2 estimate
-- statement:
--   The positive Brownian adjustment-root exponential at a bounded natural-grid stopping time has integrable square with expected square no greater than exp(sigma squared times theta squared times the physical cap). This follows from public generic grid optional sampling for theta and 2theta, and pathwise square domination.
-- source:
--   Accepted Kyprianou.Ch01.brownianGridStoppedL2Bound proof and Chapter 1 Exercise 1.10(ii) grid approximation.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianGridStoppedL2BoundPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (delta : ℝ≥0) (tau : Ω → ℕ) (N : ℕ)
    (hBound : ∀ ω, tau ω ≤ N)
    (hStop : ∀ n, n < N →
      @MeasurableSet Ω (naturalSigma X ((n : ℝ≥0) * delta))
        {ω | n < tau ω}) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let M : Ω → ℝ := fun ω =>
      Real.exp (theta * X ((tau ω : ℝ≥0) * delta) ω -
        q * (((tau ω : ℝ≥0) * delta) : ℝ))
    Integrable (fun ω => M ω ^ 2) P ∧
      (∫ ω, M ω ^ 2 ∂P) ≤
        Real.exp (sigma ^ 2 * theta ^ 2 * (((N : ℝ≥0) * delta) : ℝ)) := by sorry
