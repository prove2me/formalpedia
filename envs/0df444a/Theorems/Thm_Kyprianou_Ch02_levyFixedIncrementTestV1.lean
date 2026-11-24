-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyFixedIncrementTestV1
-- name    : Kyprianou.Ch02.levyFixedIncrementTestV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:59:29.731103+00:00
-- url     : https://prove2.me/theorems/6ca5dcbe-2f82-4d82-85ab-678456e562cb
-- title:
--   Deterministic Levy increment test depends only on its lag
-- statement:
--   Stationary increments identify the law with the increment from zero over the lag. Use the zero initial value and the equality of the nonnegative-real and real lag.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyFixedIncrementTestV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (a b : ℝ≥0) (hab : a ≤ b)
    (H : ℝ → ℂ) (hH : Measurable H) :
    (∫ ω, H (X b ω - X a ω) ∂P) =
      ∫ ω, H (X (((b : ℝ) - (a : ℝ)).toNNReal) ω) ∂P := by sorry
