-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalWeightedIntegralErrorRealClockV1
-- name    : Kyprianou.Ch04.physicalWeightedIntegralErrorRealClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:24:22.464742+00:00
-- url     : https://prove2.me/theorems/0f99fbba-ec4e-5503-8b24-8da871f51559
-- title:
--   physicalWeightedIntegralErrorRealClockV1
-- statement:
--   Physical integral difference with real-clock weights, controlled by a samplewise absolute mark ledger and the martingale perturbation.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_physicalWeightedIntegralErrorV1
import Theorems.Thm_Kyprianou_Ch04_pathWeightUniformLipschitzV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Apply the physical variation estimate to left-limit weights and the actual clock. -/

theorem Kyprianou.Ch04.physicalWeightedIntegralErrorRealClockV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j Y Z L U : NNReal → ℝ) (g : ℝ → ℝ → ℝ)
    (b K d r : ℝ) (hd : 0 ≤ d) (hK : 0 ≤ K)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T ∧ 1/2 < |j s|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ s ∈ S, Measure.dirac ((s : ℝ),j s))
    (hL : Measurable L) (hU : Measurable U)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (U t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg' : ∀ s, Differentiable ℝ (g s))
    (hKg : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (hKd : ∀ s x, 0 ≤ s → |deriv (g s) x| ≤ K)
    (A B : NNReal → ℝ) (hAB : ∀ t ≤ T, |A t - B t| ≤ r) :
    ∀ t ≤ T,
      |(b * (∫ s in Icc (0 : ℝ) (t : ℝ), g (s.toNNReal : ℝ) (L s.toNNReal)) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * g (z.1.toNNReal : ℝ) (L z.1.toNNReal) ∂ R) + A t) -
       (b * (∫ s in Icc (0 : ℝ) (t : ℝ), g s (U s.toNNReal)) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * g z.1 (U z.1.toNNReal) ∂ R) + B t)| ≤
      K * (|b| * (T : ℝ) + (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
          {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d + r := by
  sorry
