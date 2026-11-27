-- Prove2me | Theorems.Thm_Kyprianou_Ch04_normalisedWeightStateBoundV1
-- name    : Kyprianou.Ch04.normalisedWeightStateBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:33:39.591812+00:00
-- url     : https://prove2.me/theorems/d36285f3-45a4-4fb8-8dff-c5f7e6147cfc
-- title:
--   normalisedWeightStateBoundV1
-- statement:
--   Positive-time left-limit convergence and Lipschitz continuity bound normalised weights.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The normalised positive-time left weights inherit the compact state bound. -/

theorem Kyprianou.Ch04.normalisedWeightStateBoundV1 (Y Z L U : NNReal → ℝ) (T : NNReal)
    (g : ℝ → ℝ → ℝ) (K d : ℝ) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (hY : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (hZ : ∀ t, 0 < t → Tendsto Z (nhdsWithin t (Iio t)) (nhds (U t)))
    (hb : ∀ t ≤ T, |Y t-Z t| ≤ d)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |g s x-g s y| ≤ K*|x-y|) :
    ∀ t ≤ T, |(if t=0 then 0 else g t (L t))-
      (if t=0 then 0 else g t (U t))| ≤ K*d := by
  sorry
