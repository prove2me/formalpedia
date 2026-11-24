-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceBranchingLevelSetMeasurable
-- name    : Kyprianou.Ch01.sequenceBranchingLevelSetMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:56:07.413236+00:00
-- url     : https://prove2.me/theorems/87b437b1-66ac-4afb-9a4a-3088eb95c5a8
-- title:
--   Sequence branching level set is measurable
-- statement:
--   Fix a height $z$, a time $s$, and a population size $m$.
--
--   The set of interarrival/mark sequence pairs whose reverse Lamperti branching count equals $m$ is measurable in $(\mathbb{R}^{\mathbb{N}})\times(\mathbb{R}^{\mathbb{N}})$.
-- source:
--   Kyprianou (2006), Section 1.3.4; equal sequence laws give equal branching probabilities.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceBranchingLevelSetMeasurable
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    MeasurableSet
      {seq : (ℕ → ℝ) × (ℕ → ℝ) |
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (_ : Unit) => seq.1 n)
            (fun n (_ : Unit) => seq.2 n))
          s ()).toNat = m} := by
  sorry
