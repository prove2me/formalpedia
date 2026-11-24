-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceDirectBranchingCountMeasurable
-- name    : Kyprianou.Ch01.sequenceDirectBranchingCountMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:41:18.644677+00:00
-- url     : https://prove2.me/theorems/c1dcba32-5d28-4126-8620-73a729c8f0fa
-- title:
--   Direct sequence branching count is measurable
-- statement:
--   Fix a height $z$ and a time $s$. Viewing an interarrival/mark sequence pair as the sample point of the lattice walk (rather than freezing it on a singleton space), the reverse Lamperti branching count is a measurable function of the sequence pair.
-- source:
--   Kyprianou (2006), Section 1.3.4; direct-form Lamperti count on sequence space.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceDirectBranchingCountMeasurable
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.1 n)
            (fun n (σ : (ℕ → ℝ) × (ℕ → ℝ)) => σ.2 n))
          s seq).toNat) := by
  sorry
