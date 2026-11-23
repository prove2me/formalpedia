-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosivePositiveDiagonalGenerator
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosivePositiveDiagonalGenerator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:10:27.094847+00:00
-- url     : https://prove2.me/theorems/a23e2d23-49e4-4bc0-8503-363e69f34d93
-- title:
--   Positive-population holding-time diagonal derivative in nonexplosive reverse Lamperti law
-- statement:
--   For each strictly positive initial population y, the realised nonexplosive reverse Lamperti population process has diagonal transition derivative at t=0 equal to −rate·y. Prove the physical-time first-jump waiting asymptotic and control the time-changed path under the exact driver, offspring and nonexplosion assumptions. The y=0 case follows separately from the already proved branchingZeroAbsorbing and belongs in the parent bridge.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti first-jump Q-matrix diagonal

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosivePositiveDiagonalGenerator
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
    ∀ y : ℕ, 0 < y →
      HasDerivWithinAt
        (fun t : ℝ => ((K y (Real.toNNReal t)) y).toReal)
        (-((rate : ℝ) * (y : ℝ)))
        (Set.Ici 0) 0 := by
  sorry
