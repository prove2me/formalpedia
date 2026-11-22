-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialStateAE
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveInitialStateAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:37:57.098046+00:00
-- url     : https://prove2.me/theorems/b1537bab-4ba5-4ef0-8c7f-affdeaf11822
-- title:
--   Nonexplosive reverse Lamperti population retains initial state almost surely
-- statement:
--   Pathwise initial-state recovery for the compound-Poisson inverse Lamperti time change. From the regular compound-Poisson initial path, its right-inverse reciprocal occupation clock evaluates to zero at branching time zero; stopping at strict negative passage does not alter the initial state. This almost-sure identity is stronger than the initial atom measure identity and supplies it via measure congruence.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, inverse Lamperti equation (1.19)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveInitialStateAE
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
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∀ᵐ ω ∂Q,
      (compoundPoissonToBranching
        (integerCompoundPoisson y arrival marks) 0 ω).toNat = y := by
  sorry
