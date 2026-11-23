-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiPopulationPointMassTimeMeasurable
-- name    : Kyprianou.Ch01.reverseLampertiPopulationPointMassTimeMeasurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T15:32:14.822931+00:00
-- url     : https://prove2.me/theorems/698ed7cc-f45b-4c92-8bf6-e83671f8b619
-- title:
--   Borel time-measurability of one-time reverse-Lamperti population point probabilities
-- statement:
--   Each realised one-time population probability is Borel-measurable as a function of time, under the nonexplosive inverse occupation clock of the marked compound-Poisson process.
-- source:
--   Kyprianou (2006), Section 1.3.4; time measurability of nonexplosive time-changed compound-Poisson population laws, derivable from pathwise cadlag regularity and measurable process realisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiPopulationPointMassTimeMeasurable
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
    :
    ∀ z : ℕ, ∀ k : ℕ, Measurable
      (fun u : ℝ≥0 => (K z u k).toReal) := by
  sorry
