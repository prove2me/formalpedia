-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStateAEMeasurable
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:52:30.981199+00:00
-- url     : https://prove2.me/theorems/5b4cef8f-ef05-4bcd-9c85-4c110d728c6e
-- title:
--   Fixed-time a.e. measurability of the nonexplosive inverse Lamperti lattice population
-- statement:
--   Prove for every initial population and deterministic time that the exactly defined reverse Lamperti time-changed lattice compound Poisson process, converted via Int.toNat, is Q-a.e. measurable. Use existing Proved integer compound Poisson joint path regularity, measurable arrival and mark drivers, extended reciprocal occupation and its inverse, first negative passage, and random-time evaluation. The explicit non-explosion condition assures finite time changes on one common conull event. No offspring moment is assumed.
-- source:
--   Kyprianou Ch1 §1.3.4. Parent reverseLampertiNonexplosiveStateAEAndInitialMass 274da951-c8a4-49c3-a325-3820978f88fd and root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable
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
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    (∀ (y : ℕ) (t : ℝ≥0),
      AEMeasurable
        (fun ω : Ω => (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat) Q) := by
  sorry
