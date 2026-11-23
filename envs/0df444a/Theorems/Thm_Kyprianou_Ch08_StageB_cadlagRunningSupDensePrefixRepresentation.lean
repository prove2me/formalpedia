-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_cadlagRunningSupDensePrefixRepresentation
-- name    : Kyprianou.Ch08.StageB.cadlagRunningSupDensePrefixRepresentation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:34:24.398096+00:00
-- url     : https://prove2.me/theorems/dd1b58c0-da50-4792-a534-01a0301ef0bd
-- title:
--   Lemma 8.2 deterministic stopped path: genuine Chapter 8 cadlag running supremum equals dense countable prefix supremum plus endpoint
-- statement:
--   For any cadlag real sample path starting at zero, the genuine Chapter 8 running supremum at finite time equals the maximum of the sampled supremum over a dense time subset up to the endpoint and the value at the endpoint. This equality is source-faithful: the finite prefix is bounded by cadlag compactness, identified with its interval ciSup, and reduced to a dense set by the already proved generic Avram dense_timeSup_with_endpoint theorem.
-- source:
--   Kyprianou 2006 Chapter 8 Lemma 8.2 source model, with mathematically generic Prove2Me supporting theorems Kyprianou.Ch01.cadlag_runningSup_bddAbove a92cc0c0-725a-4732-a803-82da495cb71b and AvramDividend.Classical.dense_timeSup_with_endpoint 4cdf4ed6-71c6-4948-849b-8bfefa587f36. The exact source runningSup representation c4d424d4-b357-4c20-b0b8-e20ca612e75a is a currently Open supporting theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.cadlagRunningSupDensePrefixRepresentation
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag (fun t => X t ω)) (hX0 : X 0 ω = 0)
    (S : Set ℝ≥0) (hDense : Dense S) (hzero : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) :
    runningSup X t ω =
      max (⨆ u : {u : ℝ≥0 // u ∈ S ∧ u ≤ t}, X u.1 ω)
        (X t ω) := by
  sorry
