-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiBeforeInitialArrivalPopulationAE
-- name    : Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:14:11.836787+00:00
-- url     : https://prove2.me/theorems/05c27d4c-a522-4a53-b034-08f777391cd8
-- title:
--   Nonexplosive reverse Lamperti population is unchanged before its initial arrival
-- statement:
--   For each initial size y and time t, outside one Q-null set, the nonexplosive inverse Lamperti population remains at y whenever the original compound-Poisson driver's first arrival time exceeds the physical threshold y*t. This is the exact pre-first-event state lemma, including zero initial population, needed to prove the no-event contribution to independent-ancestor coupling.
-- source:
--   Kyprianou (2006), Section 1.3.4, elementary pre-first-event inverse Lamperti clock behaviour.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiBeforeInitialArrivalPopulationAE
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
    (y : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q,
      ((y : Real) * (t : Real) <
        ProbabilityTheory.arrival arrival 0 ω) →
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) t ω).toNat = y := by
  sorry
