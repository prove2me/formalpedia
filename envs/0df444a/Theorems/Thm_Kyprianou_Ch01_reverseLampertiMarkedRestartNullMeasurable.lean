-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiMarkedRestartNullMeasurable
-- name    : Kyprianou.Ch01.reverseLampertiMarkedRestartNullMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T18:39:19.869104+00:00
-- url     : https://prove2.me/theorems/58307e50-25fd-4e88-bf66-68671ec49241
-- title:
--   Null measurability of a marked restart atom
-- statement:
--   Fix an offspring index $j$. The atom on which the first mark equals $j-1$, the shifted population at height $y-1+j$ equals $k$, and the first arrival is at most $yt$, is null measurable.
-- source:
--   Kyprianou (2006), Section 1.3.4; marked first-event mixture of the nonexplosive inverse Lamperti law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiMarkedRestartNullMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (y : ℕ) (t : ℝ≥0) (k j : ℕ) :
    NullMeasurableSet {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)} Q := by
  sorry
