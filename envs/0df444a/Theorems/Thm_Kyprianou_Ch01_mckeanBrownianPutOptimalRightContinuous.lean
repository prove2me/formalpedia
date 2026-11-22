-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanBrownianPutOptimalRightContinuous
-- name    : Kyprianou.Ch01.mckeanBrownianPutOptimalRightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:26:14.263472+00:00
-- url     : https://prove2.me/theorems/b5270cde-00e6-4bae-9e9f-22b1467b136a
-- title:
--   Theorem 1.13: Brownian perpetual American put, right-continuous natural stopping times
-- statement:
--   Corrected full McKean theorem with positive exercise threshold, strict downcrossing time, pointwise right-continuous natural-filtration admissibility, integrable discounted put, exact piecewise perpetual American put value, domination over all right-continuous natural stopping times, and smooth fit. Rectifies the false raw-filtration clause of theorem 77b1f528-0069-4f4c-9fa2-4c63ac9198bd without changing the first-passage convention or payoff.
-- source:
--   Kyprianou (2006) Theorem 1.13, pp. 22-23; Perla Sousi (2011) Proposition 3.5.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanBrownianPutOptimalRightContinuous
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
      IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) ∧
      HasDerivAt (mckeanValue K barrier phi)
        (-Real.exp barrier) barrier := by
  sorry
