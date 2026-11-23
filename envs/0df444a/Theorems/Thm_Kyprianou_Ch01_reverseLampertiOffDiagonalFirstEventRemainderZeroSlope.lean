-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
-- name    : Kyprianou.Ch01.reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T12:23:34.609586+00:00
-- url     : https://prove2.me/theorems/98781b32-bef6-4438-815f-d0e672df3c56
-- title:
--   Off-diagonal Lamperti multiple-jump remainder has zero initial slope
-- statement:
--   The off-diagonal population transition minus its first-arrival offspring-mark approximation has zero right derivative at time zero, including y=0 and forbidden jump indices. Establish that the remaining multi-jump probability is o(t) by a first-jump conditioning argument and a PMF-weighted second-arrival estimate. No finite offspring moment is required.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, first-arrival and multiple-jump asymptotics for reverse Lamperti Q-matrix

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiOffDiagonalFirstEventRemainderZeroSlope
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
        (fun t : ℝ =>
          ((K y (Real.toNNReal t)) k).toReal -
            (if y ≤ k + 1 then (offspring (k + 1 - y)).toReal else 0) *
              (1 - Real.exp (-(((rate : ℝ) * (y : ℝ)) *
                (Real.toNNReal t : ℝ)))))
        0 (Set.Ici 0) 0 := by
  sorry
