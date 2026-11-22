-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNonpositivePrefixSelectedArrivalMeasurable
-- name    : Kyprianou.Ch01.firstNonpositivePrefixSelectedArrivalMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:08:12.199686+00:00
-- url     : https://prove2.me/theorems/83c6d2e6-f24b-400c-8dd1-a76bf82dbc3a
-- title:
--   Measurability of the arrival time selected by the first nonpositive mark-prefix index
-- statement:
--   For any measurable arrival-gap and jump-mark streams, select the first nonpositive prefix-length index of the integer-floor mark partial sums. The corresponding selected arrival time, at index predecessor (with Nat subtraction used for the index-zero case), is globally measurable. Reuse the Proved firstNonpositiveCompoundPrefixIndexMeasurable theorem, apply a measurable predecessor function on Nat, and use measurable_from_prod_countable_left for the arrival field as a function of sample and Nat index. This is the countable-random-time ingredient in the exact firstNonpositiveLattice hitting-clock construction, which also has separate zero-hit and infinite-hit cases.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, compound-Poisson forward Lamperti stopped path. Direct proof dependency of firstNonpositiveLatticeAEMeasurableFromDriver ea3122ce-4c2e-4917-9682-8ac701d400ca. Uses published firstNonpositiveCompoundPrefixIndexMeasurable theorem a8a74e1e-678b-4054-988b-c8f8c9e02e00. Does not assume finite offspring mean.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNonpositivePrefixSelectedArrivalMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (arrival n))
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω =>
      ProbabilityTheory.arrival arrival ((sInf {n : ℕ |
        Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}) - 1) ω) := by
  sorry
