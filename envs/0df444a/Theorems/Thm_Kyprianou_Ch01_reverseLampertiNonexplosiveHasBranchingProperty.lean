-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveHasBranchingProperty
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveHasBranchingProperty
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:30:40.032596+00:00
-- url     : https://prove2.me/theorems/3b0ab106-84f9-4f80-a694-6b6d0ee2a160
-- title:
--   Nonexplosive inverse Lamperti branching convolution property
-- statement:
--   Show that for the inverse reciprocal-occupation time-change of an explicitly nonexplosive integer compound-Poisson process with offspring jumps k−1 and jump law p, the realised population transition PMFs satisfy the independent-ancestor branching convolution law K_(y+z)(t) = K_y(t) convolution K_z(t). Requires a source-faithful branching-family decomposition and independent Poisson marks, with no finite mean assumed.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti law with explicit non-explosion, equation (1.19)

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveHasBranchingProperty
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
    HasBranchingProperty K := by
  sorry
