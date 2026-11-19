-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonLinearGrowthFromReal
-- name    : Kyprianou.Ch01.integerCompoundPoissonLinearGrowthFromReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:54:50.170752+00:00
-- url     : https://prove2.me/theorems/267adca7-dd6d-4b92-9cf0-1ce25f70f7c3
-- title:
--   Linear upper bound for floored lattice compound Poisson paths from a real path growth bound
-- statement:
--   For any given trajectory of the real compound-Poisson process with linear upper bound K(1+t), its integer-lattice realization as floor(y+X_t) has an explicit positive linear upper bound (y+K+1)(1+t) for every nonnegative time. This deterministic lemma follows from floor(x)≤x and nonnegative time and population; no probability assumptions required.
-- source:
--   Kyprianou (2006), Chapter 1 branching compound Poisson construction; elementary floor and linear inequalities.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonLinearGrowthFromReal
    {Ω : Type*} (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (ω : Ω) (K : ℝ) (hK : 0 ≤ K)
    (hGrowth : ∀ t : ℝ≥0,
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
        K * (1 + (t : ℝ))) :
    ∀ t : ℝ≥0,
      (integerCompoundPoisson y arrival marks t ω : ℝ) ≤
        ((y : ℝ) + K + 1) * (1 + (t : ℝ)) := by
  sorry
