-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoFirstArrivalReturnProbabilityLower
-- name    : Kyprianou.Ch01.reverseLampertiNoFirstArrivalReturnProbabilityLower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:11:34.424014+00:00
-- url     : https://prove2.me/theorems/5fa0019e-6f36-40d7-80c9-d6fd9c98075c
-- title:
--   No-first-arrival probability lower bound for reverse Lamperti return
-- statement:
--   Prove the probability lower bound from the already-Proved almost-sure no-first-arrival path implication. This is the first half of the two-event sandwich.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNoFirstArrivalReturnProbabilityLower
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
    ∀ y : ℕ, 0 < y → ∀ t : ℝ, 0 ≤ t →
      (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal ≤ (Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks)
          (Real.toNNReal t) ω).toNat = y}).toReal := by
  sorry
