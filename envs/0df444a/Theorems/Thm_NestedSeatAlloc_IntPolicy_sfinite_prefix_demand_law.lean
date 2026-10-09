-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_sfinite_prefix_demand_law
-- name    : NestedSeatAlloc.IntPolicy.sfinite_prefix_demand_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:01:35.189851+00:00
-- url     : https://prove2.me/theorems/c74642e4-9825-4742-be72-e7b7acf557a2
-- title:
--   The measurable higher-fare demand prefix has an s-finite marginal law
-- statement:
--   # The finite higher-fare prefix law is s-finite
--
--   IsSeatModel carries IsProbabilityMeasure P. The already Proved
--   measurable_prefix_vector theorem makes U(ω)(i)=X_i(ω),
--   for indices 1..k, a measurable vector-valued random variable.
--   The exact Mathlib theorem Measure.isProbabilityMeasure_map maps
--   IsProbabilityMeasure P to IsProbabilityMeasure (P.map U) whenever
--   U is a.e. measurable. Every probability measure is s-finite;
--   typeclass inference supplies SFinite (P.map U).
--
--   The declaration was checked using remote signature probe job
--   554e3140-c749-4486-95b9-685ccea2ad78; its expected deliberate
--   sentinel mismatch exposed the exact type of
--   Measure.isProbabilityMeasure_map.
--
--   This lemma discharges the only explicit extra premise of
--   condRevenue_integrable_next_demand and permits integral_mono_ae
--   without introducing new model assumptions. No local Lean/Lake is run.
-- source:
--   # The finite higher-fare prefix law is s-finite
--
--   IsSeatModel carries IsProbabilityMeasure P. The already Proved
--   measurable_prefix_vector theorem makes U(ω)(i)=X_i(ω),
--   for indices 1..k, a measurable vector-valued random variable.
--   The exact Mathlib theorem Measure.isProbabilityMeasure_map maps
--   IsProbabilityMeasure P to IsProbabilityMeasure (P.map U) whenever
--   U is a.e. measurable. Every probability measure is s-finite;
--   typeclass inference supplies SFinite (P.map U).
--
--   The declaration was checked using remote signature probe job
--   554e3140-c749-4486-95b9-685ccea2ad78; its expected deliberate
--   sentinel mismatch exposed the exact type of
--   Measure.isProbabilityMeasure_map.
--
--   This lemma discharges the only explicit extra premise of
--   condRevenue_integrable_next_demand and permits integral_mono_ae
--   without introducing new model assumptions. No local Lean/Lake is run.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.sfinite_prefix_demand_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    SFinite (Measure.map
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) := by sorry
