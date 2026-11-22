-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseCompoundPoissonIntegerStartsAtInitialStateAE
-- name    : Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:04:54.282466+00:00
-- url     : https://prove2.me/theorems/41d46e8f-40bd-49e2-a99c-51da7908e11e
-- title:
--   Integer compound Poisson process starts at its population count from exponential waiting-time law
-- statement:
--   For a compound-Poisson driver with positive rate, the first interarrival has an exponential distribution and is strictly positive almost surely. Reproduce the actual accepted proof of this positivity using driver law_interarrival, Measure.map_apply, expMeasure CDF at zero and `ae_iff`, without private theorem imports. Hence the initial arrival time is positive and the number of jumps by time zero is zero, using Nat.sInf_le for the jumpCount definition. The original integerCompoundPoisson y τ marks 0 ω = Int.floor(y + compoundPoisson 0 τ marks 0 ω) is therefore exactly y almost surely by unfolding compoundPoisson and piecewisePath. This is a precise source-faithful starting-state lemma, needed to prove measurable strict first-negative passage and initial atoms of the reverse Lamperti process, without a finite offspring moment.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4 reverse Lamperti; root UUID ac1b29c6-5525-4344-a03d-7469824736ed, and Open first-negative-passage clock UUID 10562bdb-b68f-4aca-a129-b9c618aca569. Reuses actual Lean source of Proved ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos UUID fa9156ce-f7ff-4366-845c-3e09c8633d1c and Proved ProbabilityTheory.compoundPoisson_ae_start UUID 95eb107c-9bdf-4676-87ac-9e5b2fa13526, but inlines their proofs because those imports have private dependency ownership and cannot be imported into the public target. Mathlib pinned at 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseCompoundPoissonIntegerStartsAtInitialStateAE
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (τ marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver τ marks rate jumpLaw Q) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      integerCompoundPoisson y τ marks 0 ω = (y : ℤ) := by
  sorry
