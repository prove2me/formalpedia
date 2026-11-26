-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteJumpGridSumDecompositionV1
-- name    : Kyprianou.Ch04.finiteJumpGridSumDecompositionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:26.767589+00:00
-- url     : https://prove2.me/theorems/1c44156e-0737-4fbc-a5f2-0c4c30984326
-- title:
--   Drift and finite atom decomposition of grid sums
-- statement:
--   Separate the drift and individual atom contributions in a finite-jump grid sum.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integration.

import Mathlib
open Finset
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteJumpGridSumDecompositionV1 {ι : Type} (S : Finset ι) (n : ℕ)
    (u v H : ℕ → ℝ) (time mark : ι → ℝ) (c : ℝ)
    (Y : ℝ → ℝ)
    (hY : ∀ t, Y t = c*t + ∑ i ∈ S, if time i ≤ t then mark i else 0)
    (huv : ∀ k ∈ range n, u k ≤ v k) :
    (∑ k ∈ range n, H k * (Y (v k) - Y (u k))) =
      c * (∑ k ∈ range n, H k * (v k - u k)) +
        ∑ i ∈ S, mark i * (∑ k ∈ range n,
          if u k < time i ∧ time i ≤ v k then H k else 0) := by
  sorry
end Kyprianou.Ch04
