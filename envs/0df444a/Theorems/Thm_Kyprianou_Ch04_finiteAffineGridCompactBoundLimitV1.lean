-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineGridCompactBoundLimitV1
-- name    : Kyprianou.Ch04.finiteAffineGridCompactBoundLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:53:04.50019+00:00
-- url     : https://prove2.me/theorems/d6ea9c2e-9f01-48ca-a690-2699cad454b6
-- title:
--   Finite affine grid convergence with compact-horizon bounded weight
-- statement:
--   Clamp the weight to the compact-horizon bound without changing any grid sample or integrals on the horizon. Apply the proved bounded finite affine grid limit.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)-(iv).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineGridCompactBoundLimitV1 (T : NNReal) (S : Finset NNReal) (j H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hC : 0 ≤ C) (hb : ∀ r ≤ T, |H r| ≤ C) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      let u := T * (i : NNReal) / (n : NNReal)
      let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
      H u * (Y v - Y u)) atTop
      (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) +
        ∑ r ∈ S, j r * H r)) := by
  sorry
end Kyprianou.Ch04
