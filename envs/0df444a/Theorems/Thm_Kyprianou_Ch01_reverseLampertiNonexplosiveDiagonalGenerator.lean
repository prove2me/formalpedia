-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveDiagonalGenerator
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveDiagonalGenerator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:35:57.70017+00:00
-- url     : https://prove2.me/theorems/babae1ca-9bbe-4f6f-9551-2bca9ae89fb0
-- title:
--   Diagonal of the nonexplosive reverse Lamperti Markov branching generator
-- statement:
--   Show the diagonal source population transition derivative at time zero equals minus y times the compound-Poisson life rate for each initial size y, including y=0. This is the no-jump holding-time asymptotics after inverse reciprocal-occupation time change, requiring a genuine small-time physical-clock estimate, without any offspring finite-moment hypothesis.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti theorem, Q-matrix from Eq. (1.19)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveDiagonalGenerator
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    ∀ y : ℕ,
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal)
        (-((rate : ℝ) * (y : ℝ)))
        (Set.Ici 0) 0 := by
  sorry
