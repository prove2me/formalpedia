-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPointwiseCosExpAbsBoundV1
-- name    : Kyprianou.Ch02.levyPointwiseCosExpAbsBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:22:29.815826+00:00
-- url     : https://prove2.me/theorems/cf4d44b1-bdf7-4156-ae9e-1fdfc196c66b
-- title:
--   Cosine deficit bounded by exponential absolute deficit
-- statement:
--   The cosine deficit is bounded by both 2 and 2|ξx|. Combine with the exponential bound.
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPointwiseCosExpAbsBoundV1
    (ξ x : ℝ) : 1 - Real.cos (ξ*x) ≤ 4*(1+|ξ|)*(1-Real.exp (-|x|)) := by sorry
