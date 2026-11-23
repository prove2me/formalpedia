-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalOneArrivalEventError
-- name    : Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalEventError
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:52:41.564658+00:00
-- url     : https://prove2.me/theorems/edbf201e-bdd7-41bb-b968-3fc58ad2e89b
-- title:
--   Off-diagonal reverse Lamperti one-arrival approximation with two-arrival error event
-- statement:
--   For k≠y, compare the actual time-changed population atom to the event that the first jump occurs by original clock time y*t and has offspring mark k+1-y. Their symmetric difference requires at least two arrivals before the physical branching horizon. This yields an absolute probability error bounded by the union of first marked arrivals and a second arrival before its corresponding y+j time upper bound. Handle the y=0 and forbidden-index cases and use non-explosion only to identify the path after the inverse clock.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, inverse Lamperti first-jump path decomposition and first-two-arrival event inclusion

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalEventError
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
    ∀ (y k : ℕ), k ≠ y → ∀ (t : ℝ), 0 ≤ t →
      |((K y (Real.toNNReal t)) k).toReal -
        (if y ≤ k + 1 then (Q {ω | marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ)}).toReal else 0)| ≤
        (Q {ω | ∃ j : ℕ,
          marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ)}).toReal := by
  sorry
