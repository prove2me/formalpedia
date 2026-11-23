-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalShiftedTailPathwise
-- name    : Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T16:22:12.501636+00:00
-- url     : https://prove2.me/theorems/a320c6f5-17d4-4dda-9fcf-acd2e9a5c0ef
-- title:
--   Pathwise reverse-Lamperti restart after the first marked arrival
-- statement:
--   On the first physical arrival before branching time t, the reverse-Lamperti process restarts from state y-1 plus the initial offspring count, driven by the shifted marked interarrival sequence, at the residual branching time.
-- source:
--   Kyprianou (2006), Section 1.3.4; exact first-event pathwise decomposition of the nonexplosive inverse Lamperti law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstArrivalShiftedTailPathwise
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
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    ∀ᵐ ω ∂Q, ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) →
      (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat =
      (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat := by
  sorry
