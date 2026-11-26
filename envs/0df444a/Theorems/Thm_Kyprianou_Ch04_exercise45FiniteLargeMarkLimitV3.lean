-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45FiniteLargeMarkLimitV3
-- name    : Kyprianou.Ch04.exercise45FiniteLargeMarkLimitV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:23.46042+00:00
-- url     : https://prove2.me/theorems/d862ae5b-be11-5a77-b9e8-0da471bfe1b4
-- title:
--   exercise45FiniteLargeMarkLimitV3
-- statement:
--   exercise45FiniteLargeMarkLimitV3
-- source:
--   Exercise 4.5(iii), physical cutoff limit

import Mathlib
open MeasureTheory Filter Set Topology
open scoped MeasureTheory NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45FiniteLargeMarkLimitV3
(R : Measure (ℝ × ℝ)) (t : NNReal) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r)
    (hR : R.restrict (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ) (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hConv : ∀ s : NNReal, 0 < s → Tendsto (fun n => L n s) atTop (nhds (Y s))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 * g z.1 (L n z.1.toNNReal) ∂ R) atTop
      (nhds (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * g z.1 (Y z.1.toNNReal) ∂ R)) := by
  sorry
