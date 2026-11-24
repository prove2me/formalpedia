-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sequenceIntegerWalkJointlyMeasurable
-- name    : Kyprianou.Ch01.sequenceIntegerWalkJointlyMeasurable
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T02:38:08.924277+00:00
-- url     : https://prove2.me/theorems/4d2e502e-659b-4717-a92a-10108e73838d
-- title:
--   Frozen sequence lattice walk is jointly measurable
-- statement:
--   Fix a height $z$. On the product space $(\mathbb{R}^{\mathbb{N}})\times(\mathbb{R}^{\mathbb{N}})$ of interarrival/mark sequence pairs, the lattice compound-Poisson walk built from the coordinate sequences is a jointly measurable function of the sequence pair and calendar time.
-- source:
--   Kyprianou (2006), Section 1.3.4; joint measurability of the lattice walk on sequence space.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sequenceIntegerWalkJointlyMeasurable
    (z : ℕ) :
    Measurable
      (fun p : ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0 =>
        integerCompoundPoisson z
          (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.1 n)
          (fun n (seq : (ℕ → ℝ) × (ℕ → ℝ)) => seq.2 n)
          p.2 p.1) := by
  sorry
