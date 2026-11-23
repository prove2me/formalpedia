-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalMultipleArrivalErrorBound
-- name    : Kyprianou.Ch01.reverseLampertiOffDiagonalMultipleArrivalErrorBound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:44:23.166612+00:00
-- url     : https://prove2.me/theorems/9d637ecd-63af-43e2-bbba-cff53c3c729e
-- title:
--   Quantitative two-arrival error bound for reverse Lamperti off-diagonal transitions
-- statement:
--   Bound the absolute discrepancy between the off-diagonal transition probability at physical branching time t and its first marked jump approximation by rate*y*t times the probability-weighted second-arrival factor. Identify first-jump marks and show that all trajectories differing from the first-arrival approximation require another arrival before the time-changed terminal clock. This event containment and its two-clock probability estimate are the core stochastic obligations; include y=0 and forbidden indices.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, compound-Poisson first-two-arrival control under inverse Lamperti clock

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiOffDiagonalMultipleArrivalErrorBound
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
    ∀ (y k : ℕ), k ≠ y → ∀ (t : ℝ), 0 ≤ t →
      |((K y (Real.toNNReal t)) k).toReal -
        (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
          (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
            (Real.toNNReal t : ℝ))))| ≤
        ((rate : ℝ) * (y : ℝ)) * t *
          (∑' j : ℕ, (offspring j).toReal *
            (1 - Real.exp (-((rate : ℝ) * (((y + j : ℕ) : ℝ)) * t)))) := by
  sorry
