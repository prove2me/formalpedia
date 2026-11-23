-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
-- name    : Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:00:04.10753+00:00
-- url     : https://prove2.me/theorems/2cccaff4-2206-445b-89b0-dad3825b6dcc
-- title:
--   Reverse Lamperti post-first-arrival return correction is o(t) under source no-jump path law
-- statement:
--   For a source nonexplosive reverse Lamperti population with no neutral offspring and exact independent exponential interarrivals and marks, assume the independently provable pathwise fact that the integer compound Poisson surplus remains at initial y before first raw arrival. For every y>0 the probability of returning to y after the first raw event has zero right derivative at time zero. Establish by conditioning on the first mark and bounding the chance of a second event using exponential survival and dominated convergence; no finite offspring mean. The added pathwise premise is independently proved by importing the public Avram first-arrival certificate, reducing the open stochastic argument to the truly two-jump rarity estimate.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4 reverse Lamperti nonexplosive generator, conditioning on nonneutral first jump and stochastic second-jump o(t) return.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlopeGivenNoJumpPath
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hBefore : ∀ (z : ℕ) (u : ℝ≥0) (ω : Ω),
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
        integerCompoundPoisson z arrival marks u ω = (z : ℤ)) :
    ∀ y : ℕ, 0 < y →
      HasDerivWithinAt
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
              ProbabilityTheory.arrival arrival 0 ω}).toReal)
        0 (Set.Ici 0) 0 := by
  sorry
