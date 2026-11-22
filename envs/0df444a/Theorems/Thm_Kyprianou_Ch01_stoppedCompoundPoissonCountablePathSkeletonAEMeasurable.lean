-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stoppedCompoundPoissonCountablePathSkeletonAEMeasurable
-- name    : Kyprianou.Ch01.stoppedCompoundPoissonCountablePathSkeletonAEMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:37:00.015823+00:00
-- url     : https://prove2.me/theorems/47203b98-0dac-4651-b3f8-ba78ee69eb19
-- title:
--   Almost-everywhere measurable countable skeleton of the stopped lattice compound-Poisson path
-- statement:
--   For any countable sequence of nonnegative real sampling times, the stopped integer compound Poisson process yields an almost-everywhere measurable ℕ-indexed integer-valued random path. Prove coordinatewise using the existing stoppedCompoundPoissonMarkov theorem, which supplies almost-sure nonnegativity and fixed-time almost-everywhere measurability of the natural-number representation. Cast back to the original integer on the corresponding conull set, then assemble with aemeasurable_pi_iff, valid because the skeleton index ℕ is countable. This helps construct a common measurable representative of the full càdlàg path from a rational/dyadic time grid.
-- source:
--   Proved parent premise Kyprianou.Ch01.stoppedCompoundPoissonMarkov 0e97933c-a2d7-4f59-a9c5-782003be5f5f; source-bound stopped driver obligation 49405927-66dc-442e-b14c-6d9558559823 for Kyprianou (2006) Ch01 §1.3.4. The first full uncountable-index direct argument CE candidate 45792 revealed that aemeasurable_pi_iff needs a countable index; this theorem repairs the exact mathematical interface by restricting to a countable skeleton.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stoppedCompoundPoissonCountablePathSkeletonAEMeasurable
    {Ω' : Type*} [MeasurableSpace Ω']
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hRate : 0 < rate)
    (offspring : PMF ℕ) (hNoNullJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω' → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hDriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ (y : ℕ) (times : ℕ → ℝ≥0),
      AEMeasurable (fun ω : Ω' => fun n : ℕ =>
        stoppedIntegerCompoundPoisson y arrival marks (times n) ω) Q := by
  sorry
