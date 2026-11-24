-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBVForcesFirstJumpMomentV1
-- name    : Kyprianou.Ch02.levyBVForcesFirstJumpMomentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:37:57.395617+00:00
-- url     : https://prove2.me/theorems/6f36bcff-749c-404f-a595-c1ef43134b1e
-- title:
--   Almost-sure bounded-variation Lévy paths force finite truncated absolute first jump moment
-- statement:
--   The process-level necessity that the actual Lévy jump measure has integrable min(1, abs(x)) when almost all real-valued Lévy sample paths have locally bounded variation. It must account for infinitely active positive and negative jumps, whose total variation cannot cancel, and use the prescribed characteristic triplet under the original source hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyBVForcesFirstJumpMomentV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) →
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure := by
  sorry
