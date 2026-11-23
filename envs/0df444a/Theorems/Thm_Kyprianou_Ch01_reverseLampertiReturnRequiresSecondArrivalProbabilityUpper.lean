-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnRequiresSecondArrivalProbabilityUpper
-- name    : Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalProbabilityUpper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:11:28.492805+00:00
-- url     : https://prove2.me/theorems/49021eac-b371-4973-a171-69b565ba0d47
-- title:
--   Return after first reverse Lamperti jump requires timely second arrival
-- statement:
--   Prove the stochastic upper half of the original two-event return-probability sandwich. With no neutral marks, a first jump changes population and return requires the second arrival, or first passage to zero prevents return. No finite offspring moment assumption.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalProbabilityUpper
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
      (Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks)
          (Real.toNNReal t) ω).toNat = y}).toReal ≤ (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
        ProbabilityTheory.arrival arrival 0 ω}).toReal + (Q {ω | ∃ k : ℕ,
          marks 0 ω = (k : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + k : ℕ) : ℝ)) * (Real.toNNReal t : ℝ)}).toReal := by
  sorry
