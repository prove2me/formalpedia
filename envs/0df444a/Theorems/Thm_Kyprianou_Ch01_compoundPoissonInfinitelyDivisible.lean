-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonInfinitelyDivisible
-- name    : Kyprianou.Ch01.compoundPoissonInfinitelyDivisible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:09:32.503196+00:00
-- url     : https://prove2.me/theorems/88e6b6de-c4dd-4541-88b8-701b424e595f
-- title:
--   §1.2.2 — compound Poisson infinite divisibility
-- statement:
--   Kyprianou §1.2.2, pp. 5–7: every marginal law of a compound Poisson process with positive rate, independent identically distributed jumps and a probability jump law without atom at zero is infinitely divisible. Draft theorem uses LeanLevy's compound Poisson driver predicate; proof is outstanding. Every process, law and rate variable is explicitly quantified; compound Poisson exponent uses the direct compound-Poisson characteristic function instead of an unavailable triple exponent field.
-- source:
--   Kyprianou (2006), §1.2.2, pp. 5–7; LeanLevy, Processes/CompoundPoissonLaw.lean, frozen GitHub source commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible

open MeasureTheory Filter Finset ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem Kyprianou.Ch01.compoundPoissonInfinitelyDivisible
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) :
    IsInfinitelyDivisible
      (μ.map (compoundPoisson b τ Y (t : ℝ))) := by
  sorry
