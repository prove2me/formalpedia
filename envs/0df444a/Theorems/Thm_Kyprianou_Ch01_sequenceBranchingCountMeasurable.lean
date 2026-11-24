-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceBranchingCountMeasurable
-- name    : Kyprianou.Ch01.sequenceBranchingCountMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T02:31:09.987143+00:00
-- url     : https://prove2.me/theorems/35c73a42-0ba8-4cd2-8efc-6dcfbc90e1c2
-- title:
--   Branching count of a sequence pair is measurable
-- statement:
--   Fix a height $z$ and a time $s$. The map sending an interarrival/mark sequence pair to the reverse Lamperti branching count at that height and time is a measurable function on $(\mathbb{R}^{\mathbb{N}})\times(\mathbb{R}^{\mathbb{N}})$.
-- source:
--   Kyprianou (2006), Section 1.3.4; measurability of the Lamperti functional on sequence space.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceBranchingCountMeasurable
    (z : ℕ) (s : ℝ≥0) :
    Measurable
      (fun seq : (ℕ → ℝ) × (ℕ → ℝ) =>
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n (_ : Unit) => seq.1 n)
            (fun n (_ : Unit) => seq.2 n))
          s ()).toNat) := by
  sorry
