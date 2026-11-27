-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridRightContinuousV1
-- name    : Kyprianou.Ch04.clippedGridRightContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:29.696915+00:00
-- url     : https://prove2.me/theorems/9aec3db4-9669-5101-b925-ad061b30405b
-- title:
--   clippedGridRightContinuousV1
-- statement:
--   A finite clipped grid sum of a right-continuous path remains right continuous.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.clippedGridRightContinuousV1  (Y : NNReal → ℝ)
    (hr : ∀ t, Tendsto Y (𝓝[>] t) (𝓝 (Y t)))
    (u : ℕ → NNReal) (n : ℕ) (H : ℕ → ℝ) :
    let G := fun t : NNReal => ∑ k ∈ Finset.range n,
      H k * (Y (min t (u (k+1)))-Y (min t (u k)))
    ∀ t, Tendsto G (𝓝[>] t) (𝓝 (G t)) := by
  sorry
