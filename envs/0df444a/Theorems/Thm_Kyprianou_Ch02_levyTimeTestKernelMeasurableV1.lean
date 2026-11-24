-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyTimeTestKernelMeasurableV1
-- name    : Kyprianou.Ch02.levyTimeTestKernelMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:59:27.521329+00:00
-- url     : https://prove2.me/theorems/39fb406c-72b4-4473-9ce8-cd3598a56720
-- title:
--   Measurable bounded-test time kernel of a Levy process
-- statement:
--   Use the universal measurable right-continuous path evaluator and a measurable version of the whole path. Integrating the resulting jointly measurable test over the probability space produces a measurable kernel, equal at each time to the original kernel.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyTimeTestKernelMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (H : ℝ → ℂ) (hH : Measurable H) :
    Measurable (fun r : ℝ => ∫ ω, H (X r.toNNReal ω) ∂P) := by sorry
