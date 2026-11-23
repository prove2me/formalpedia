-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiIndependentAncestorPositiveTimeLaw
-- name    : Kyprianou.Ch01.reverseLampertiIndependentAncestorPositiveTimeLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:27:52.146322+00:00
-- url     : https://prove2.me/theorems/c08054a0-c77e-4f4c-873f-a18b2055a8c1
-- title:
--   Positive-time independent-ancestor convolution for nonexplosive inverse Lamperti populations
-- statement:
--   For every strictly positive time t, the nonexplosive inverse Lamperti process with a+b initial individuals has the same one-time law as the sum of two independent copies started from a and b. The time-zero case has been eliminated using the already-proved initial atom law. Prove the positive-time claim by constructing independent ancestral lineages from the iid exponential clock and offspring marks, or by a first-jump renewal uniqueness argument. No finite offspring moment is assumed.
-- source:
--   Kyprianou (2006) Section 1.3.4, nonexplosive reverse Lamperti branching construction at strictly positive times.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiIndependentAncestorPositiveTimeLaw
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
        (compoundPoissonToBranching
          (integerCompoundPoisson (a + b) arrival marks) t ω).toNat = k} =
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} := by
  sorry
