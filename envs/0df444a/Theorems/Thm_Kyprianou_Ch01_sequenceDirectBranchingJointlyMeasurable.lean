-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingJointlyMeasurable
-- name    : Kyprianou.Ch01.sequenceDirectBranchingJointlyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:27:27.139809+00:00
-- url     : https://prove2.me/theorems/55ed74a1-0722-43ea-9cfc-6acda05cf7bb
-- title:
--   Direct sequence branching is jointly measurable
-- statement:
--   Fix a height $z$. The reverse Lamperti population built from the lattice walk on interarrival/mark sequence space is jointly measurable in the sequence pair and calendar time.
-- source:
--   Kyprianou (2006), Section 1.3.4; joint Lamperti image on sequence space.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceDirectBranchingJointlyMeasurable
    (z : ℕ) :
    Measurable
      (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
        compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          p.2 p.1) := by
  sorry
