-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNonpositiveCompoundPrefixIndexMeasurable
-- name    : Kyprianou.Ch01.firstNonpositiveCompoundPrefixIndexMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:05:09.148069+00:00
-- url     : https://prove2.me/theorems/a8a74e1e-678b-4054-988b-c8f8c9e02e00
-- title:
--   The first nonpositive finite-prefix lattice index of measurable compound Poisson marks is measurable
-- statement:
--   For any measurable sequence of real-valued jump marks and a nonnegative integer initial population y, the least natural-number prefix length n at which the integer floor of y plus the sum of the first n marks is nonpositive is a measurable random variable. The convention is that the infimum of the empty subset of Nat equals 0. Each finite prefix sum is measurable; characterise the event that the least index equals a specified k as an intersection of the k-th nonpositive event and the previous positive events, or the empty-hit event with k=0. This is the countable index-selection ingredient of the exact first-nonpositive lattice passage time of the driver.
-- source:
--   Kyprianou 2006, Ch01 §1.3.4; concrete proof prerequisite of firstNonpositiveLatticeAEMeasurableFromDriver ea3122ce-4c2e-4917-9682-8ac701d400ca, which is the sole hard dependency in stopped driver path AEMeasurable child 49405927-66dc-442e-b14c-6d9558559823. Reuses actual accepted natural-number sInf fibre construction from source of ProbabilityTheory.measurable_jumpCount_arrival, but imports no private Prove2Me theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNonpositiveCompoundPrefixIndexMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (marks : ℕ → Ω → ℝ)
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω =>
      sInf {n : ℕ |
        Int.floor ((y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) ≤ 0}) := by
  sorry
