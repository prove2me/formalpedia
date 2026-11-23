-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
-- name    : Kyprianou.Ch01.reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:07:58.761411+00:00
-- url     : https://prove2.me/theorems/f30d5b59-e350-468e-8209-be8c4050873e
-- title:
--   No-initial-jump contribution to independent-ancestor law
-- statement:
--   For paths whose initial compound-Poisson clock has not yet rung, the single population from a+b ancestors has exactly the same singleton-state probability as the sum of two independently sampled populations conditioned on neither of their initial clocks ringing.
-- source:
--   Kyprianou (2006), Section 1.3.4, exact first-event decomposition of nonexplosive reverse Lamperti population.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiIndependentAncestorBeforeFirstArrivalContribution
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
    (a b : ℕ) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    Q {ω |
        (((a + b : Nat) : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ω) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        ((a : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.1 ∧ (b : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.2) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  sorry
