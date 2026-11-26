-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IndependentLevelTransferV23
-- name    : Kyprianou.Ch04.exercise41IndependentLevelTransferV23
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:06:14.431804+00:00
-- url     : https://prove2.me/theorems/2655b191-4944-4951-b615-4f5171f4da5e
-- title:
--   Transfer a null product-level section to a pair with the same joint law
-- statement:
--   Transfer a null product-level section to a pair with the same joint law
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41IndependentLevelTransferV23
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hLaw : Measure.map (fun w => (f w,g w)) P = (Measure.map f P).prod μ)
    (h : ∀ᵐ p ∂P.prod μ, f p.1 + p.2 ≠ 0) :
    ∀ᵐ w ∂P, f w + g w ≠ 0 := by
  sorry
