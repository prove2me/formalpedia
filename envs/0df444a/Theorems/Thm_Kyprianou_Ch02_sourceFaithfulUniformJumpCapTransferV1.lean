-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulUniformJumpCapTransferV1
-- name    : Kyprianou.Ch02.sourceFaithfulUniformJumpCapTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:22:35.142905+00:00
-- url     : https://prove2.me/theorems/bfe710ff-75fb-4b99-b536-346d911b2c89
-- title:
--   A common strict jump cap passes to a compact-uniform limit
-- statement:
--   Choose δ positive with c+2δ<1. Uniform closeness at t and on its left neighbourhood bounds the difference between the values and between the left limits, respectively, by δ. The triangle inequality gives the result.
-- source:
--   Kyprianou (2006), Chapter 2, proof of Theorem 2.1, small-jump process

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem sourceFaithfulUniformJumpCapTransferV1
    (F : ℕ → ℝ≥0 → ℝ) (f : ℝ≥0 → ℝ)
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (c : ℝ) (hc : c < 1)
    (hcap : ∀ n, ∃ l : ℝ,
      Tendsto (F n) (nhdsWithin t (Set.Iio t)) (nhds l) ∧ |F n t - l| ≤ c)
    (huni : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ s : ℝ≥0, s ≤ T → |F n s - f s| < δ)
    (l : ℝ) (hl : Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)) :
    |f t - l| < 1 := by sorry
end Kyprianou.Ch02
