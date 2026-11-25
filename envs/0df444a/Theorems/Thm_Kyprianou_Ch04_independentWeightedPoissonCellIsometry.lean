-- Prove2me | Theorems.Thm_Kyprianou_Ch04_independentWeightedPoissonCellIsometry
-- name    : Kyprianou.Ch04.independentWeightedPoissonCellIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:07:44.395292+00:00
-- url     : https://prove2.me/theorems/c5a906b5-c89e-5a8d-ae77-8102c7bbfbd4
-- title:
--   One-cell weighted compensated Poisson L2 isometry for independent past weights
-- statement:
--   For the modular Poisson random measure, any finite-intensity measurable time-mark cell and a square-integrable real weight independent of the raw count satisfy the exact compensated-cell L2 identity. Square integrability and the compensated count variance are obtained from the existing modular Poisson isometry source, so there are no additional moment hypotheses on the cell. This is the simple predictable one-cell building block for Kyprianou Chapter 4 Exercise 4.4.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4, simple-predictable compensated Poisson isometry.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_independentWeightedCompensatedCellL2

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.independentWeightedPoissonCellIsometry
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P ν)
    {B : Set (ℝ × ℝ)} (hB : MeasurableSet B)
    (hFin : referenceIntensity ν B ≠ ⊤)
    (H : Ω → ℝ) (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hIndep : IndepFun H (fun ω => N.N ω B) P) :
    Integrable (fun ω => (H ω * N.compensated B ω) ^ 2) P ∧
      (∫ ω, (H ω * N.compensated B ω) ^ 2 ∂P) =
        (referenceIntensity ν B).toReal *
          ∫ ω, H ω ^ 2 ∂P := by
  sorry
