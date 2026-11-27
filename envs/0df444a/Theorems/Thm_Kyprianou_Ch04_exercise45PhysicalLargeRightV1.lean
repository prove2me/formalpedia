-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalLargeRightV1
-- name    : Kyprianou.Ch04.exercise45PhysicalLargeRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:32:40.089909+00:00
-- url     : https://prove2.me/theorems/0f1be6d7-a777-44cc-af92-6f7592789a87
-- title:
--   Right continuity of the original drift and large-jump path
-- statement:
--   The physical drift and retained large-jump integral is right-continuous almost surely by the finite affine step representation.
-- source:
--   Kyprianou Exercise 4.5, reconstruction

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The physical large jump and drift process is right-continuous almost surely. -/
theorem Kyprianou.Ch04.exercise45PhysicalLargeRightV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L : NNReal → Ω → ℝ)
    (b : ℝ) (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w) :
    let V : NNReal → Ω → ℝ := fun t w => b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w)
    ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => V s w) (Ici t) t := by
  sorry
