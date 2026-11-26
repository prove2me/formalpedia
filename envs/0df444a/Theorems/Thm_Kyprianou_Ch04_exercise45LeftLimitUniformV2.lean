-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45LeftLimitUniformV2
-- name    : Kyprianou.Ch04.exercise45LeftLimitUniformV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:09:39.61214+00:00
-- url     : https://prove2.me/theorems/58af218b-41a4-5533-aa76-a15a684289ce
-- title:
--   exercise45LeftLimitUniformV2
-- statement:
--   exercise45LeftLimitUniformV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45LeftLimitUniformV2
    (U : ℕ → NNReal → ℝ) (L : ℕ → NNReal → ℝ)
    (X Y : NNReal → ℝ)
    (hL : ∀ n t, 0 < t → Tendsto (U n) (nhdsWithin t (Iio t)) (nhds (L n t)))
    (hY : ∀ t, 0 < t → Tendsto X (nhdsWithin t (Iio t)) (nhds (Y t)))
    (hConv : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |U n t-X t| < δ) :
    ∀ t : NNReal, 0 < t → Tendsto (fun n => L n t) atTop (nhds (Y t)) := by
  sorry
