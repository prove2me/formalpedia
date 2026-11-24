-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingZMeasurable
-- name    : Kyprianou.Ch01.sequenceDirectBranchingZMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:50:31.339498+00:00
-- url     : https://prove2.me/theorems/69275d26-7727-406e-be6b-c73128de2eb8
-- title:
--   Direct sequence branching population is measurable
-- statement:
--   Fix a height $z$ and a time $s$. The reverse Lamperti population read from the lattice walk driven by an interarrival/mark sequence pair is a measurable $\mathbb{Z}$-valued function of that sequence pair.
-- source:
--   Kyprianou (2006), Section 1.3.4; integer population before taking toNat.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceDirectBranchingZMeasurable
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          s seq) := by
  sorry
