-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnAfterFirstArrivalZeroSlope
-- name    : Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:12:39.092061+00:00
-- url     : https://prove2.me/theorems/aacecf3f-bfb5-49a4-a4e3-4d5e15c1bb36
-- title:
--   Return-to-initial-population probability after a first arrival has zero right slope
-- statement:
--   For an initial positive population y under the exact nonexplosive reverse Lamperti construction with no neutral offspring (offspring(1)=0), the difference between the probability that the population equals its starting value at branching time t and the probability of no compound-Poisson arrival before the initial linear clock y*t has right derivative zero at t=0. A return after the first non-neutral jump requires a second branching event; the second-event probability is o(t) by conditioning on the possibly unbounded offspring mark and dominated convergence, without a finite offspring mean. This is the genuine stochastic part of the positive diagonal Q-generator derivation.
-- source:
--   Kyprianou (2006) §1.3.4 reverse Lamperti first-event expansion and second-jump negligible return, with explicit nonexplosion and no finite offspring moments.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiReturnAfterFirstArrivalZeroSlope
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ y : ℕ, 0 < y →
      HasDerivWithinAt
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
              ProbabilityTheory.arrival arrival 0 ω}).toReal)
        0 (Set.Ici 0) 0 := by
  sorry
