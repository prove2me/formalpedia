-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPutOptimal
-- name    : Kyprianou.Ch01.mckeanBrownianPutOptimal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:16:02.032662+00:00
-- url     : https://prove2.me/theorems/77b1f528-0069-4f4c-9fa2-4c63ac9198bd
-- title:
--   Theorem 1.13: McKean's Brownian perpetual American put, optimal stopping and smooth fit
-- statement:
--   Exact Chapter 1 optimal stopping application: a continuous real Lévy process with Brownian drift γ and volatility σ>0, natural-filtration stopping times allowing infinite waiting, and payoff e^(−qτ)(K−e^{x+Xτ})⁺. The theorem identifies the optimal first passage below x*=log(K Φ(q)/(1+Φ(q))) where Φ(q)=(sqrt(γ²+2σ²q)+γ)/σ², gives the entire piecewise value function for every starting log-price x, proves dominance over all natural stopping times, and asserts the smooth-fit derivative at the barrier. Draft uncompiled; random-path measurability and filtration details must be validated. The stopping-time assertion is formulated for an everywhere-continuous sample-path version of the Brownian process, strengthening the a.s.-continuous baseline to ensure raw natural-filtration measurability.
-- source:
--   Kyprianou (2006), Chapter 1, Theorem 1.13, pp. 22–23, equations (1.14)–(1.16).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBrownianPutOptimal
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
    0 < phi ∧
      IsNaturalStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier := by
  sorry
