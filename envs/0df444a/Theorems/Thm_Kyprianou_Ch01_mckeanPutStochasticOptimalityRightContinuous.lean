-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanPutStochasticOptimalityRightContinuous
-- name    : Kyprianou.Ch01.mckeanPutStochasticOptimalityRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:26:14.512996+00:00
-- url     : https://prove2.me/theorems/9a56cd50-3536-495a-8e23-68ab4beb476d
-- title:
--   Theorem 1.13: stochastic McKean optimal put verification with right-continuous stopping times
-- statement:
--   Source-faithful four-conjunct stochastic verification of the Brownian perpetual American put and strict lower-passage barrier, for all admissible stopping times of the right-continuous natural filtration F(t+). Includes barrier stopping-time admissibility, integrability, expected-value equality and universal optimality. Replaces the open raw-filtration child 781ac8d5-bc9e-4baa-b783-b9035f85d750 whose stopping-time assertion is false generally.
-- source:
--   Kyprianou (2006), Ch. 1 Theorem 1.13; Perla Sousi (2011) Advanced Probability, Example 3.2 and Proposition 3.5.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanPutStochasticOptimalityRightContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) := by sorry
