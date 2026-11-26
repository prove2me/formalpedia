-- Prove2me | Theorems.Thm_Kyprianou_Ch04_affineLeftPathMeasurableV1
-- name    : Kyprianou.Ch04.affineLeftPathMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:38:03.136055+00:00
-- url     : https://prove2.me/theorems/9157c1cb-8a47-56d2-a228-bef42c4d4c2a
-- title:
--   Time measurability of positive-time left limits of locally finite affine-step paths
-- statement:
--   Time measurability of positive-time left limits of locally finite affine-step paths
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem affineLeftPathMeasurableV1 {ι : Type} (U L : NNReal → ℝ)
    (hU : ∀ n : ℕ, ∃ (S : Finset ι) (r a : ι → ℝ) (c d : ℝ),
      ∀ t : NNReal, t ≤ (n : NNReal) →
        U t = c + d * (t : ℝ) + ∑ i ∈ S, if r i ≤ (t : ℝ) then a i else 0)
    (hL : ∀ t : NNReal, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t))) :
    Measurable L := by
  sorry
end Kyprianou.Ch04
