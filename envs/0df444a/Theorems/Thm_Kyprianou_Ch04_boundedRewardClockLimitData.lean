-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedRewardClockLimitData
-- name    : Kyprianou.Ch04.boundedRewardClockLimitData
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:48:58.67206+00:00
-- url     : https://prove2.me/theorems/133080bc-296e-4e52-a8a0-7a68459f0d53
-- title:
--   boundedRewardClockLimitData
-- statement:
--   A bounded decreasing measurable reward has a limiting deterministic mean. Its exponential-clock product mean has the same limit, by clock averaging and disintegration.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.boundedRewardClockLimitData
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (hga : ∀ w, Antitone (fun t : NNReal => g (t,w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (herr : ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0)) :
    ∃ ell : ℝ,
      Tendsto (fun t : NNReal => ∫ w, g (t,w) ∂P) atTop (nhds ell) ∧
      Tendsto (fun n : ℕ => ∫ z : Ω × ℝ, g (z.2.toNNReal,z.1) ∂(P.prod (expMeasure (q n)))) atTop (nhds ell) := by
  sorry
