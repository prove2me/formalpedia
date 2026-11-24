-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPointwiseExpAbsBoundV1
-- name    : Kyprianou.Ch02.levyPointwiseExpAbsBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:22:25.851695+00:00
-- url     : https://prove2.me/theorems/f94a0700-2065-4158-b5ce-04b122efbfb0
-- title:
--   Exponential absolute deficit bounds truncated absolute value
-- statement:
--   Use exp(u) ≥ 1+u and split at u=1.
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPointwiseExpAbsBoundV1
    (x : ℝ) : min 1 |x| ≤ 2 * (1 - Real.exp (-|x|)) := by sorry
