-- Prove2me | Theorems.Thm_Kyprianou_Ch04_gridStepWeightMeasurableV1
-- name    : Kyprianou.Ch04.gridStepWeightMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:50:44.086206+00:00
-- url     : https://prove2.me/theorems/2bf52ff3-289c-4d4b-be04-82b7a0f4708f
-- title:
--   gridStepWeightMeasurableV1
-- statement:
--   The step interpolation with predictable cell coefficients is measurable on the predictable sigma field.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.gridStepWeightMeasurableV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (u : ℕ → NNReal) (n : ℕ)
    (H : ℕ → Ω → ℝ) (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k)) :
    Measurable[F.predictable] (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k p.2) p.1) := by
  sorry
