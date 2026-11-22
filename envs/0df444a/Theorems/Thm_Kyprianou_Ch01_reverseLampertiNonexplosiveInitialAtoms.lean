-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveInitialAtoms
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveInitialAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:52:20.852912+00:00
-- url     : https://prove2.me/theorems/6600b9f2-8246-40a4-8b22-81afa12bd113
-- title:
--   Initial-state singleton probabilities of the nonexplosive reverse Lamperti population
-- statement:
--   Show the exact reverse Lamperti process starts in its prescribed integer y state almost surely, by integer compound-Poisson X_0=y, the right-continuous initial path, inverse reciprocal occupation at level zero, and absence of negative passage at the initial time. Deduce that Q of its kth state event at t=0 equals the pure Dirac PMF δ_y(k). Reuse the existing Proved compoundPoisson_ae_start theorem and relevant reciprocal clock and first-passage lemmas, without assuming finite offspring mean.
-- source:
--   Kyprianou Ch1 §1.3.4, same parent 274da951-c8a4-49c3-a325-3820978f88fd, root ac1b29c6-5525-4344-a03d-7469824736ed, proved ProbabilityTheory.compoundPoisson_ae_start 95eb107c-9bdf-4676-87ac-9e5b2fa13526.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveInitialAtoms
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
    ∀ (y k : ℕ),
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
        (PMF.pure y) k := by
  sorry
