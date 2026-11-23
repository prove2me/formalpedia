-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorAfterFirstArrivalContribution
-- name    : Kyprianou.Ch01.reverseLampertiIndependentAncestorAfterFirstArrivalContribution
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T13:07:54.586415+00:00
-- url     : https://prove2.me/theorems/87b6abee-ed67-4257-8d7b-1c5ad04c1c78
-- title:
--   Post-initial-jump contribution to independent-ancestor law
-- statement:
--   For paths on which the initial compound-Poisson clock has rung, the single population from a+b ancestors and the independently sampled sum have identical state-k event probabilities, with the product-space event requiring at least one of the two initial clocks to have rung. The proof needs a genuine independent-mark restart or stopped-jump-chain uniqueness argument.
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

theorem Kyprianou.Ch01.reverseLampertiIndependentAncestorAfterFirstArrivalContribution
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
        Not (((a + b : Nat) : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ω) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        Not ((a : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.1 ∧ (b : Real) * (t : Real) < ProbabilityTheory.arrival arrival 0 ζ.2) ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  sorry
