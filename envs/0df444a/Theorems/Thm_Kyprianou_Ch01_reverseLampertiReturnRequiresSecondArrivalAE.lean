-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiReturnRequiresSecondArrivalAE
-- name    : Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T17:29:42.924264+00:00
-- url     : https://prove2.me/theorems/ad0722c8-49bc-455b-8009-e29068443a9c
-- title:
--   Pathwise reverse Lamperti return after first jump requires a second arrival
-- statement:
--   Almost-sure pathwise implication for the exact nonexplosive inverse Lamperti process: returning to a positive starting population either precedes the first driver jump, or involves an offspring-supported non-neutral first jump and a sufficiently early second arrival. Prove by the piecewise integer compound-Poisson trajectory, the Proved positive-stage inverse-clock jump lemma and the extinction zero-stage case, with no finite offspring mean. This source-faithful helper isolates the stochastic event inclusion underlying the original upper probability bound.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiReturnRequiresSecondArrivalAE
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
    (hBefore : ∀ (z : ℕ) (u : ℝ≥0) (ω : Ω),
      (u : ℝ) < ProbabilityTheory.arrival arrival 0 ω →
        integerCompoundPoisson z arrival marks u ω = (z : ℤ)) :
    ∀ (y : ℕ) (t : ℝ≥0), 0 < y →
      ∀ᵐ ω ∂Q,
        (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = y →
        (y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω ∨
        ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤ (y : ℝ) * (t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              (((y + j : ℕ) : ℝ)) * (t : ℝ) := by
  sorry
