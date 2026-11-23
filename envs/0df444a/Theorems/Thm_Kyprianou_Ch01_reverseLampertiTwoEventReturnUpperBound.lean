-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiTwoEventReturnUpperBound
-- name    : Kyprianou.Ch01.reverseLampertiTwoEventReturnUpperBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:14:01.758836+00:00
-- url     : https://prove2.me/theorems/00d9b390-e08c-46c5-9a90-0d2e03dd72fc
-- title:
--   Exact reverse Lamperti post-first-event rare-return upper bound
-- statement:
--   For every y>0 in the original nonexplosive inverse Lamperti population, the excess return probability above first-arrival survival is between zero and rate*y*t times the offspring average 1-exp(-rate*(y+k)*t). Prove via the first two independent exponential interarrival clocks and first offspring mark, with no finite mean assumption. This is the substantive stochastic child.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiTwoEventReturnUpperBound
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
      (0 ≤ ((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω}).toReal) ∧
      (((K y (Real.toNNReal t)) y).toReal -
          (Q {ω | (y : ℝ) * (Real.toNNReal t : ℝ) <
            ProbabilityTheory.arrival arrival 0 ω}).toReal) ≤
        ((rate : ℝ) * (y : ℝ)) * t * (∑' k : ℕ, (offspring k).toReal *
          (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t)))) := by
  sorry
