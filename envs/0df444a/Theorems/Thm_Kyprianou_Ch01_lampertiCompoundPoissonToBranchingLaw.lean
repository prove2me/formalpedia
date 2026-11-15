-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiCompoundPoissonToBranchingLaw
-- name    : Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:18:03.132201+00:00
-- url     : https://prove2.me/theorems/6c308a61-4553-4120-ad0f-ee8f113bc0c2
-- title:
--   §1.3.4: reverse Lamperti construction identifies the Markov branching semigroup
-- statement:
--   Reverse Lamperti correspondence of Kyprianou Chapter 1, equation (1.19): start a real-valued compound-Poisson process at integer y with independent rate-λ jumps from the offspring-minus-one distribution supported on {-1,0,1,...}, with the book's no-zero-jumps assumption p₁=0. Applying the inverse reciprocal occupation clock and stopping at the negative barrier gives the nonexplosive continuous-time Markov branching transition law. The target equates the resulting time-t distribution for all initial populations y and all t with the unique branching Markov semigroup characterised independently by the branching property, Chapman–Kolmogorov law and Q-matrix rates λy p_(k+1−y). A finite offspring mean ensures nonexplosion. The desired distributional equality does not occur among the hypotheses. This is a substantial uncompiled draft and the full forward path-law converse remains separate.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, printed pp. 25–26, equation (1.19), reverse time-change discussion and Definition 1.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (hFiniteMean : Summable
      (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  sorry
