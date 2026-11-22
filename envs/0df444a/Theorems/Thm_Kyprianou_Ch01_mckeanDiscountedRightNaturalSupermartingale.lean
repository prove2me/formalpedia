-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightNaturalSupermartingale
-- name    : Kyprianou.Ch01.mckeanDiscountedRightNaturalSupermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:14:46.641819+00:00
-- url     : https://prove2.me/theorems/701ed4a9-5f98-4acb-b062-e3129b0e0ee5
-- title:
--   Discounted Brownian McKean candidate value is a supermartingale in the right-natural filtration
-- statement:
--   The actual discounted McKean candidate value process is a supermartingale under the natural right-continuous filtration of the drifted Brownian log-price. The filtration F is explicitly assumed equal to naturalSigmaRight of the shifted Brownian process at every time, and fixed-time measurability plus path continuity and IsLinearBrownian are retained. Prove the process adapted and integrable using the established bounded value function, then establish the eventwise Brownian supermartingale inequality using the smooth-fit value, the proved generator characteristic-root identity, the exercise-region generator inequality, and a genuine stopped Itô or equivalent semigroup argument. This is the main stochastic original source obligation.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13, Brownian put verification by discounted supermartingale.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedRightNaturalSupermartingale
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
    Supermartingale
      (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)) F P := by sorry
