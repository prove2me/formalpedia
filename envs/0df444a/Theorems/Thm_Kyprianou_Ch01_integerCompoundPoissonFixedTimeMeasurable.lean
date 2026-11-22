-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonFixedTimeMeasurable
-- name    : Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:50:43.681186+00:00
-- url     : https://prove2.me/theorems/4a215c58-846c-47b2-990a-fad256013ece
-- title:
--   Measurable fixed-time integer-valued compound-Poisson lattice process
-- statement:
--   For arbitrary measurable arrival gaps and jump marks, the integer-valued lattice compound Poisson process obtained by taking the floor of its real-valued compound Poisson process with initial population y has a globally measurable section at each deterministic nonnegative time. Reuse the Proved ProbabilityTheory.measurable_compoundPoisson and Mathlib's measurability of the integer floor. This establishes the foundational deterministic-time measurable component needed to prove that the stopped lattice path is a measurable product-space random variable, without offspring moment conditions or exceptional null sets.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; supports Open stopped driver path-measurability theorem UUID 49405927-66dc-442e-b14c-6d9558559823, child of the SKETCH_ACCEPTED forward Lamperti correspondence; source definition integerCompoundPoisson from Definitions.Def_Kyprianou_Ch01_BranchingGenerator; proved source ProbabilityTheory.measurable_compoundPoisson UUID 8b9b747f-5209-4e8d-b4f4-4520348f19c2.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (arrival n))
    (hMarks : ∀ n, Measurable (marks n))
    (t : ℝ≥0) :
    Measurable (integerCompoundPoisson y arrival marks t) := by
  sorry
