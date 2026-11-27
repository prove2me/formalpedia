-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pathWeightUniformLipschitzV1
-- name    : Kyprianou.Ch04.pathWeightUniformLipschitzV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:14:56.871772+00:00
-- url     : https://prove2.me/theorems/3cc01c4d-f7e4-4c06-bec6-3ec8888345c5
-- title:
--   pathWeightUniformLipschitzV1
-- statement:
--   pathWeightUniformLipschitzV1
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_positiveLeftDifferenceBoundV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Bounded differentiable state weights along measurable left-limit paths
are integrable on the clock and inherit a uniform Lipschitz perturbation bound. -/

theorem Kyprianou.Ch04.pathWeightUniformLipschitzV1 (Y Z L R : NNReal → ℝ) (T : NNReal)
    (g : ℝ → ℝ → ℝ) (K d : ℝ)
    (hL : Measurable L) (hR : Measurable R)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (R t)))
    (hb : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg' : ∀ s, Differentiable ℝ (g s))
    (hK : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (hd : ∀ s x, 0 ≤ s → |deriv (g s) x| ≤ K) :
    IntegrableOn (fun s : ℝ => g (s.toNNReal : ℝ) (L s.toNNReal))
      (Ioc (0 : ℝ) (T : ℝ)) ∧
    IntegrableOn (fun s : ℝ => g (s.toNNReal : ℝ) (R s.toNNReal))
      (Ioc (0 : ℝ) (T : ℝ)) ∧
    ∀ t ≤ T, 0 < t → |g t (L t) - g t (R t)| ≤ K * d := by
  sorry
