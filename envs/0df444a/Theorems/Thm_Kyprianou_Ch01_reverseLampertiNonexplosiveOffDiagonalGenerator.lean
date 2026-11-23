-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveOffDiagonalGenerator
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveOffDiagonalGenerator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:35:44.369874+00:00
-- url     : https://prove2.me/theorems/b853ea06-24c1-42f1-af90-9a73eaa8d5de
-- title:
--   Off-diagonal transitions of the nonexplosive reverse Lamperti branching generator
-- statement:
--   Show that a population of y individuals makes an off-diagonal transition to k at small branching time with first-order rate y times the compound-Poisson life rate times offspring probability p_(k+1−y), zero for forbidden negative offspring indices. Prove the one-mark transition and negligible two-or-more-mark contribution after the stopped inverse clock, with the exact explicit non-explosion condition and no finite offspring mean.
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

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveOffDiagonalGenerator
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
    ∀ (y k : ℕ), k ≠ y →
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) k).toReal)
        (if y ≤ k + 1 then
          (rate : ℝ) * (y : ℝ) *
            (offspring (k + 1 - y)).toReal
         else 0)
        (Set.Ici 0) 0 := by
  sorry
