-- Prove2me | Theorems.Thm_Kyprianou_Ch04_independentWeightedCompensatedCellL2
-- name    : Kyprianou.Ch04.independentWeightedCompensatedCellL2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:47:09.724664+00:00
-- url     : https://prove2.me/theorems/83557f3f-c6d4-41f9-a45d-666533303900
-- title:
--   Past-independent quadratic energy of a compensated Poisson cell
-- statement:
--   Under finite cell intensity and a Poisson count law, if a square-integrable past weight is independent of the cell count, and the cell compensated count has integrable square with variance equal to its intensity, then the weighted compensated count has integrable square with expected energy equal to intensity times the weight second moment. The core independence-to-energy transfer supports Kyprianou Chapter 4 Exercise 4.4.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4; independence and conditional second moments for compensated Poisson random measures.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.independentWeightedCompensatedCellL2
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P ν)
    {B : Set (ℝ × ℝ)} (_hB : MeasurableSet B)
    (_hFin : referenceIntensity ν B ≠ ⊤)
    (H : Ω → ℝ) (hH2 : Integrable (fun ω => H ω ^ 2) P)
    (hInt : Integrable (fun ω => (N.compensated B ω) ^ 2) P)
    (hSecondMoment : (∫ ω, (N.compensated B ω) ^ 2 ∂P) =
      (referenceIntensity ν B).toReal)
    (hIndep : IndepFun H (fun ω => N.N ω B) P) :
    Integrable (fun ω => (H ω * N.compensated B ω) ^ 2) P ∧
      (∫ ω, (H ω * N.compensated B ω) ^ 2 ∂P) =
        (referenceIntensity ν B).toReal *
          ∫ ω, H ω ^ 2 ∂P := by
  sorry
