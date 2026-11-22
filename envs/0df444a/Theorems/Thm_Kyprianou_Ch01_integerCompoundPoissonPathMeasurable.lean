-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonPathMeasurable
-- name    : Kyprianou.Ch01.integerCompoundPoissonPathMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:58:50.940977+00:00
-- url     : https://prove2.me/theorems/dd5645a6-ca3c-45fb-98ca-9ffbf760a024
-- title:
--   Globally measurable integer-valued compound-Poisson path in the product sigma-algebra
-- statement:
--   The lattice-valued compound Poisson process with measurable arrival gaps and marks defines a globally measurable random path as a function to the integer-valued product path space indexed by all nonnegative times. Product-space measurability is characterised by fixed-time measurable sections, even for an uncountable time index. Apply the newly Proved Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable theorem at every t. This is the unstopped-path ingredient needed for the first-nonpositive stopping operator.
-- source:
--   Prove2Me accepted theorem Kyprianou.Ch01.integerCompoundPoissonFixedTimeMeasurable UUID 4a215c58-846c-47b2-990a-fad256013ece, submission 1230eb36-1eb2-4e0d-bd37-42fc9e80b2b5. Supports stopped driver path child 49405927-66dc-442e-b14c-6d9558559823 of Kyprianou (2006) Chapter 1 §1.3.4 no-mean forward Lamperti correspondence.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonPathMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n, Measurable (arrival n))
    (hMarks : ∀ n, Measurable (marks n)) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      integerCompoundPoisson y arrival marks t ω) := by
  sorry
