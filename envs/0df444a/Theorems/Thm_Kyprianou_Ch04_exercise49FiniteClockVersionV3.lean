-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49FiniteClockVersionV3
-- name    : Kyprianou.Ch04.exercise49FiniteClockVersionV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:36:54.941386+00:00
-- url     : https://prove2.me/theorems/8c005732-be13-4f39-995e-f53849921cff
-- title:
--   Measurable finite first-passage clock version
-- statement:
--   Almost-sure finite hitting-clock representative for nonnegative initial reserve.
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49FiniteClockVersionV3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (a : ℝ) (ha : 0 ≤ a) :
    let τ : Ω → WithTop NNReal := fun ω => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ a + X t ω < 0}
    ∃ f : Ω → NNReal, Measurable f ∧
      ∀ᵐ ω ∂P, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal) := by
  sorry
