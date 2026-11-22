-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightConditionalTransitionValue
-- name    : Kyprianou.Ch01.mckeanRightConditionalTransitionValue
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:32:22.829317+00:00
-- url     : https://prove2.me/theorems/c304c8fb-9ec5-455a-b903-b3cb0804f962
-- title:
--   Brownian right-natural conditional expectation of McKean payoff equals the Lévy transition integral
-- statement:
--   Under the exact drifted Brownian Lévy process with all continuous paths, the discounted McKean candidate at a later time has conditional expectation given the natural right-continuous filtration equal to the deterministic discount times the stationary-increment transition integral starting from the current state. A key issue is independence from the RIGHT filtration, which follows from independent increments at times u>s followed by u↓s and continuity. Reuse Proved Kyprianou.Ch01.levyIncrement_indep_naturalSigma, stationary-increment law, measurable bounded McKean payoff and conditional expectation of an independent random variable. No replacement of F by a smaller ordinary natural filtration is permitted.
-- source:
--   Kyprianou (2006), Ch 1 Thm 1.13, Markov property for Brownian right-natural filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightConditionalTransitionValue
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    ∀ s t : ℝ≥0, s ≤ t →
      P[(fun ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) | F s] =ᵐ[P]
      (fun ω => Real.exp (-q * (t : ℝ)) *
        ∫ ξ, mckeanValue K barrier phi
          ((x + X s ω) + X (t - s) ξ) ∂P) := by sorry
