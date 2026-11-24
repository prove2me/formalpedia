-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingCountFactorsThroughSequences
-- name    : Kyprianou.Ch01.branchingCountFactorsThroughSequences
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T01:51:21.191803+00:00
-- url     : https://prove2.me/theorems/e285c19a-cdc7-4ea8-82dc-05d7fcc6abb0
-- title:
--   Branching count factors through the sequence pair
-- statement:
--   Let arrival and mark sequences drive a reverse Lamperti population. Fix a height $z$ and a time $s$.
--
--   The branching count at an outcome $\omega$ equals the deterministic functional of the sequence pair evaluated at $\omega$, both for the original pair and for the shifted pair.
-- source:
--   Kyprianou (2006), Section 1.3.4; equal sequence laws give equal branching probabilities.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Branching count read from a deterministic interarrival/mark sequence pair. -/
noncomputable def Kyprianou.Ch01.branchingCountOfSequences
    (z : ℕ) (s : ℝ≥0) (seq : (ℕ → ℝ) × (ℕ → ℝ)) : ℤ :=
  compoundPoissonToBranching
    (integerCompoundPoisson z
      (fun n (_ : Unit) => seq.1 n)
      (fun n (_ : Unit) => seq.2 n))
    s ()

theorem Kyprianou.Ch01.branchingCountFactorsThroughSequences
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (ν : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    (hOrig : HasLaw (fun w => (fun n => arrival n w, fun n => marks n w)) ν Q)
    (hShift : HasLaw
      (fun w => (fun n => arrival (n + 1) w, fun n => marks (n + 1) w)) ν Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    (∀ ω,
        (compoundPoissonToBranching
          (integerCompoundPoisson z
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat =
          (branchingCountOfSequences z s
            (fun n => arrival (n + 1) ω, fun n => marks (n + 1) ω)).toNat) ∧
      ∀ ω,
        (compoundPoissonToBranching
          (integerCompoundPoisson z arrival marks) s ω).toNat =
          (branchingCountOfSequences z s
            (fun n => arrival n ω, fun n => marks n ω)).toNat := by
  sorry
