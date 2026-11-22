-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardPathMapsAEMeasurableWithoutMoment
-- name    : Kyprianou.Ch01.lampertiForwardPathMapsAEMeasurableWithoutMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:20:56.011881+00:00
-- url     : https://prove2.me/theorems/d346ccdb-3e68-4130-b078-6746f99dd872
-- title:
--   Forward Lamperti path maps are almost-everywhere measurable without offspring moments
-- statement:
--   Under the full Markov-branching and compound-Poisson driver hypotheses of the forward Lamperti correspondence, the inverse-occupation-clock transformed branching path and the stopped integer compound Poisson path are almost-everywhere measurable into the integer-valued product path space, under their respective probability measures. The branching càdlàg hypothesis is only almost sure, so the logically appropriate conclusion is AEMeasurable rather than globally Measurable. On conull càdlàg trajectory sets, rational-time approximations establish measurability of random-time evaluation and of stopping; no finite first offspring moment is assumed.
-- source:
--   Corrected, source-faithful path-map measurability obligation for Kyprianou (2006) Chapter 1 §1.3.4 forward Lamperti law, theorem 318afc19-2086-4e20-9846-225169aaa3c1. The original c79965ce-c470-48ca-a8ce-26e523ad6e21 asserts global Measurable from a.e. càdlàg and appears too strong on exceptional paths; the corrected theorem supplies the exact AEMeasurable premises of public theorem a97e3cd9-54b5-4b63-8e1c-43118f511d7c.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardPathMapsAEMeasurableWithoutMoment
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws)
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (hBranching : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovPath Y P law)
    (hSemigroup : IsPopulationMarkovSemigroup law)
    (hGenerator : IsBranchingRateGenerator law rate offspring)
    (hInitial : ∀ y : ℕ, P y {ω | Y 0 ω = y} = 1)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ y : ℕ, ∀ᵐ ω ∂P y,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ y : ℕ,
      AEMeasurable
        (fun ω : Ω => fun t : ℝ≥0 =>
          (branchingToPoisson Y t ω : ℤ)) (P y) ∧
      AEMeasurable
        (fun ω : Ω' => fun t : ℝ≥0 =>
          stoppedIntegerCompoundPoisson y arrival marks t ω) Q := by
  sorry
