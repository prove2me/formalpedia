-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveConstructsBranchingLaw
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveConstructsBranchingLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:31:53.824956+00:00
-- url     : https://prove2.me/theorems/add9a198-d73d-4166-b02f-7086a5eb80b0
-- title:
--   Reverse Lamperti compound Poisson time change constructs a conservative branching semigroup with exact generator
-- statement:
--   Given the exact hypotheses of Kyprianou Chapter 1 §1.3.4 reverse Lamperti theorem, including the explicit global non-explosion assumption for the reciprocal occupation clock and integer-supported compound-Poisson marks, construct the transition law K(y,t) of the nonnegative natural-valued inverse-time-changed paths. Prove K is genuinely a PopulationLaws (each fixed-time probability distribution is a PMF, hence conservative), satisfies the branching convolution property and time-homogeneous Markov Chapman-Kolmogorov semigroup law, has deterministic initial state, and has exactly the branching generator q(y,k)=lambda*y*(p(k+1-y)) off diagonal and -lambda*y on diagonal with p_1=0. Prove the point probability K y t k equals the exact supplied Q event of (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k, not a synthetic process or law. Use existing proved compoundPoissonReverseRecoveryPathwise, compoundPoisson Markov laws, first-passage and clock results, and the explicit non-explosion condition. This is the substantive reverse stochastic-process construction obligation connected through a root SKETCH_ACCEPTED proof.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti construction; definitions Def_Kyprianou_Ch01_LampertiInverse, Def_Kyprianou_Ch01_BranchingGenerator. Main mission 9919725d-217e-48cb-9cd1-bb779a69b820, parent target ac1b29c6-5525-4344-a03d-7469824736ed. Existing proved compoundPoissonReverseRecoveryPathwise 41fefac4-5573-460f-ba9d-981ea052b900 and integer compound Poisson/clock lemmas; requires full path measurability and Markov generator reasoning.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveConstructsBranchingLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω) :
    ∃ K : PopulationLaws,
      HasBranchingProperty K ∧
      IsPopulationMarkovSemigroup K ∧
      (∀ y : ℕ, K y 0 = PMF.pure y) ∧
      IsBranchingRateGenerator K rate offspring ∧
      ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
        K y t k =
          Q {ω | (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  sorry
