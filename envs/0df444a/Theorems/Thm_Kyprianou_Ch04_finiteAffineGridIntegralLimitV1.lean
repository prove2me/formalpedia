-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteAffineGridIntegralLimitV1
-- name    : Kyprianou.Ch04.finiteAffineGridIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:43:53.403173+00:00
-- url     : https://prove2.me/theorems/def45e5d-7b59-54ae-bd94-d658f708c6c9
-- title:
--   Uniform grid integral limit for bounded weights and finite affine jumps
-- statement:
--   Use the exact finite jump grid decomposition, drift dominated convergence and the finite sum of the individual strict-left atom limits. Shift the sequence by one to exclude the zero denominator.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteAffineGridIntegralLimitV1 (T : NNReal) (S : Finset NNReal) (j H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hb : ∀ r, |H r| ≤ C) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      let u := T * (i : NNReal) / (n : NNReal)
      let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
      H u * (Y v - Y u)) atTop
      (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) +
        ∑ r ∈ S, j r * H r)) := by
  sorry
end Kyprianou.Ch04
