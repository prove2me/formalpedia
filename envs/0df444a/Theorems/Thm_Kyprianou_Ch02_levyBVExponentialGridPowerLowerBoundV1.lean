-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBVExponentialGridPowerLowerBoundV1
-- name    : Kyprianou.Ch02.levyBVExponentialGridPowerLowerBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:46:44.363723+00:00
-- url     : https://prove2.me/theorems/5fa8aea3-7540-4989-be49-983941549a73
-- title:
--   Bounded variation forces uniformly positive exponential transform powers of fine increments
-- statement:
--   For any original real Levy process with almost surely locally bounded variation, the powers of its exponentially damped absolute increment expectation at times 1/(n+1) admit one strictly positive lower bound for all n. This is independent of the characteristic triplet. The absolute sum along each uniform partition of [0,1] is bounded by path variation; obtain a measurable positive lower bound for all exponential partition sums and factor their expectations using stationary independent increments.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyBVExponentialGridPowerLowerBoundV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1) := by
  sorry
