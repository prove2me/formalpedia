-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
-- name    : Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:11:52.369687+00:00
-- url     : https://prove2.me/theorems/8804474f-52a6-4a1f-9ba2-5fefc5be3eea
-- title:
--   Pathwise off-diagonal one-arrival agreement outside the two-arrival exceptional event
-- statement:
--   Under the exact inverse Lamperti and nonexplosion hypotheses, outside the exceptional event of first two compound-Poisson arrivals before the marked physical clock, the realised population equals off-diagonal state k precisely when the first arrival occurred before y*t with mark k+1-y. Establish this almost surely for each y,k and t, including zero initial population and forbidden offspring indices, using first-arrival path identities and stopped inverse clock properties.
-- source:
--   Kyprianou (2006) Ch1 §1.3.4, pathwise first-jump approximation under inverse reciprocal-occupation time change

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiOffDiagonalOneArrivalAEAgreementOutsideSecond
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
      ∀ᵐ ω ∂Q,
        (¬ (∃ j : ℕ,
          marks 0 ω = (j : ℝ) - 1 ∧
          ProbabilityTheory.arrival arrival 0 ω ≤
            (y : ℝ) * (Real.toNNReal t : ℝ) ∧
          ProbabilityTheory.arrival arrival 1 ω ≤
            ProbabilityTheory.arrival arrival 0 ω +
              ((y + j : ℕ) : ℝ) * (Real.toNNReal t : ℝ))) →
          ((compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks)
            (Real.toNNReal t) ω).toNat = k ↔
            y ≤ k + 1 ∧
            marks 0 ω = ((k + 1 - y : ℕ) : ℝ) - 1 ∧
            ProbabilityTheory.arrival arrival 0 ω ≤
              (y : ℝ) * (Real.toNNReal t : ℝ)) := by
  sorry
