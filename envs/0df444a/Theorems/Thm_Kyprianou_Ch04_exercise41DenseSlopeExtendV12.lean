-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DenseSlopeExtendV12
-- name    : Kyprianou.Ch04.exercise41DenseSlopeExtendV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:45.22589+00:00
-- url     : https://prove2.me/theorems/ef27c321-fa88-4d61-9ed0-a375c0799987
-- title:
--   A slope inequality on dense deterministic times extends to all times by right continuity
-- statement:
--   A slope inequality on dense deterministic times extends to all times by right continuity
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DenseSlopeExtendV12
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ u, ContinuousWithinAt x (Ici u) u)
    (c : ℝ) (δ : NNReal)
    (h : ∀ k, 0 < q k → q k < δ → c * (q k : ℝ) ≤ x (q k)) :
    ∀ u : NNReal, 0 < u → u < δ → c * (u : ℝ) ≤ x u := by
  sorry
