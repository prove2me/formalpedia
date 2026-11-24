-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_uncapped_stopped_parameter_kernel
-- name    : Kyprianou.Ch08.StageB.p2m810_uncapped_stopped_parameter_kernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:03:06.844811+00:00
-- url     : https://prove2.me/theorems/95c15ea6-df3c-4b08-a3d3-716b5d757320
-- title:
--   Apply dominated convergence to both capped stopped-kernel integrals, whose equality follows from the finite stopped product law.
-- statement:
--   Apply dominated convergence to both capped stopped-kernel integrals, whose equality follows from the finite stopped product law.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_uncapped_stopped_parameter_kernel
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime F τ)
    (H : (ℝ≥0 × ℝ) × (ℝ≥0 → ℝ) → ℝ) (hH : Measurable H)
    (hb : ∀ z, 0 ≤ H z ∧ H z ≤ 1) :
    (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) 0 (fun t : ℝ≥0 =>
      H ((t,X.X t ω),fun s => X.X (t+s) ω - X.X t ω)) (τ ω) ∂P) =
    ∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) 0 (fun t : ℝ≥0 =>
      (∫ η, H ((t,X.X t ω),fun s => X.X s η) ∂P)) (τ ω) ∂P := by
  sorry
