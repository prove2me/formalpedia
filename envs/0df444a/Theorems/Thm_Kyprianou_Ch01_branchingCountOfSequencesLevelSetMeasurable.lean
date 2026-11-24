-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCountOfSequencesLevelSetMeasurable
-- name    : Kyprianou.Ch01.branchingCountOfSequencesLevelSetMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:52:42.970799+00:00
-- url     : https://prove2.me/theorems/23341cd3-3de6-4735-af99-4cd327bb6a0d
-- title:
--   Level set of the sequence branching count is measurable
-- statement:
--   Fix a height $z$, a time $s$, and a population size $m$.
--
--   The set of interarrival/mark sequence pairs whose deterministic branching count equals $m$ is measurable in $(\mathbb{R}^{\mathbb{N}})\times(\mathbb{R}^{\mathbb{N}})$.
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

noncomputable def Kyprianou.Ch01.branchingCountOfSequences
    (z : ℕ) (s : ℝ≥0) (seq : (ℕ → ℝ) × (ℕ → ℝ)) : ℤ :=
  compoundPoissonToBranching
    (integerCompoundPoisson z
      (fun n (_ : Unit) => seq.1 n)
      (fun n (_ : Unit) => seq.2 n))
    s ()

theorem Kyprianou.Ch01.branchingCountOfSequencesLevelSetMeasurable
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    MeasurableSet
      {seq : (ℕ → ℝ) × (ℕ → ℝ) |
        (branchingCountOfSequences z s seq).toNat = m} := by
  sorry
