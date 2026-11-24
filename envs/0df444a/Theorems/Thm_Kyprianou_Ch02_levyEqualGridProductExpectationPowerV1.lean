-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyEqualGridProductExpectationPowerV1
-- name    : Kyprianou.Ch02.levyEqualGridProductExpectationPowerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:04:14.815396+00:00
-- url     : https://prove2.me/theorems/42c02087-5e9d-46a6-9776-55e5d1e33d91
-- title:
--   Expectations of products on an equal Lévy grid are powers of a single-cell expectation
-- statement:
--   Apply independence of grid increments, stationarity, and the product integral theorem.
-- source:
--   Kyprianou (2006), Exercise 2.8: Laplace factorisation of positive and negative variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyEqualGridProductExpectationPowerV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    let g (k : ℕ) := t*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    let d (k : ℕ) (ω : Ω) := X (g (k+1)) ω-X (g k) ω
    (∫ ω, ∏ i : Fin (n+1), f (d i.val ω) ∂P) =
      (∫ ω, f (X (t/((n+1 : ℕ) : ℝ≥0)) ω) ∂P)^(n+1) := by sorry
