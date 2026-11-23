-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonShiftAfterFirstMark
-- name    : Kyprianou.Ch01.integerCompoundPoissonShiftAfterFirstMark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:04:18.338911+00:00
-- url     : https://prove2.me/theorems/79a48480-64ab-4e0e-b69e-4b66842cc258
-- title:
--   Integer compound-Poisson path restarts after first marked arrival
-- statement:
--   For an integer compound-Poisson path with strictly increasing arrival epochs tending to infinity, shifting the path after its first arrival recovers the integer compound-Poisson process driven by the subsequent interarrivals and marks, with new nonnegative initial population y-1+j when the first mark equals j-1. This is the deterministic path component needed by the corrected reverse-Lamperti first-arrival restart theorem.
-- source:
--   Kyprianou (2006) Section 1.3.4 first-jump decomposition; independently formalised sourceAfterFirstMark helper in accepted sketch ab6b38f1-4537-409e-a4ee-2f550d8904fd.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Finset
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonShiftAfterFirstMark
    {Ω : Type*} (y j : ℕ) (arrival marks : ℕ → Ω → ℝ) (ω : Ω)
    (hy : 0 < y)
    (hMono : StrictMono (fun n => ProbabilityTheory.arrival arrival n ω))
    (hTop : Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop)
    (hMark : marks 0 ω = (j : ℝ) - 1)
    (u : ℝ≥0)
    (hu : ProbabilityTheory.arrival arrival 0 ω ≤ (u : ℝ)) :
    integerCompoundPoisson y arrival marks u ω =
      integerCompoundPoisson ((y - 1) + j)
        (fun n w => arrival (n + 1) w)
        (fun n w => marks (n + 1) w)
        (Real.toNNReal ((u : ℝ) - ProbabilityTheory.arrival arrival 0 ω)) ω := by
  sorry
