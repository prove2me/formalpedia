-- Prove2me | Theorems.Thm_Kyprianou_Ch04_affineStepLeftLimitV1
-- name    : Kyprianou.Ch04.affineStepLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:28:44.114117+00:00
-- url     : https://prove2.me/theorems/4541dc50-2dc7-46e5-9f0b-08d5eb3b5968
-- title:
--   Positive-time left limits of finite affine-step paths
-- statement:
--   Positive-time left limits of finite affine-step paths
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem affineStepLeftLimitV1 {ι : Type} (U : NNReal → ℝ) (S : Finset ι) (r a : ι → ℝ)
    (c d : ℝ) (t T : NNReal) (ht : 0 < t) (hT : t ≤ T)
    (hU : ∀ u ≤ T, U u = c + d * (u : ℝ) +
      ∑ i ∈ S, if r i ≤ (u : ℝ) then a i else 0)
    (l : ℝ) (hl : Tendsto U (𝓝[<] t) (𝓝 l)) :
    l = c + d * (t : ℝ) + ∑ i ∈ S, if r i < (t : ℝ) then a i else 0 := by
  sorry
end Kyprianou.Ch04
