-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorOneTimeLaw
-- name    : Kyprianou.Ch01.reverseLampertiIndependentAncestorOneTimeLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T10:56:05.862606+00:00
-- url     : https://prove2.me/theorems/761cf5d4-2d30-4d5d-9059-e679379111bb
-- title:
--   One-time independent-ancestor coupling of nonexplosive reverse Lamperti populations
-- statement:
--   For arbitrary initial ancestor counts a and b, the exact source nonexplosive reverse Lamperti population started from a+b has at every t the same law as the sum of two independently sampled reverse Lamperti populations started from a and b. Express the law as equality of explicit single-state event measures under Q and the product Q×Q. Prove by an independent-ancestor construction or a first-jump renewal argument using the iid exponential/mark driver, without a finite offspring moment assumption. This is the genuine remaining stochastic branching property, stronger and more constructive than an unproved abstract HasBranchingProperty assumption.
-- source:
--   Kyprianou (2006), §1.3.4 discrete reverse Lamperti branching construction, explicit time-marginal independent-ancestor coupling under the original compound-Poisson driver.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiIndependentAncestorOneTimeLaw
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
    (a b : ℕ) (t : ℝ≥0) (k : ℕ) :
    Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  sorry
