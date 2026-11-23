-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBoundedVariationNecessityV1
-- name    : Kyprianou.Ch02.levyBoundedVariationNecessityV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:54:21.306638+00:00
-- url     : https://prove2.me/theorems/b9cbac0c-4f51-47e2-80da-ddf67c0c1efd
-- title:
--   Necessity in Lévy bounded-variation criterion: no Brownian part and finite truncated first moment
-- statement:
--   For a genuine Lévy process with the exact prescribed characteristic exponent, almost surely locally bounded-variation paths force Gaussian coefficient σ to vanish and the Lévy measure to have integrable min(1, |x|). A proof must exclude Brownian quadratic-variation paths and the possibility that infinite variation of small jumps cancels pathwise; use Lévy-Itô uniqueness and the source path-variation argument.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyBoundedVariationNecessityV1
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
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) := by
  sorry
