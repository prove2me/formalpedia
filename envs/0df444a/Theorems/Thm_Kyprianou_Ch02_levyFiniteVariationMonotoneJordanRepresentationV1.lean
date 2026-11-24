-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyFiniteVariationMonotoneJordanRepresentationV1
-- name    : Kyprianou.Ch02.levyFiniteVariationMonotoneJordanRepresentationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:35:01.881803+00:00
-- url     : https://prove2.me/theorems/d623bcd3-5bf2-4124-8137-e1ca2a96a328
-- title:
--   Zero-Gaussian finite-small-jump Lévy process admits almost-sure pathwise monotone Jordan representation
-- statement:
--   For the original real Lévy process with the actual prescribed triplet exponent, zero Gaussian coefficient and integrable truncated absolute Lévy jump measure imply that almost every full sample path can be written at all nonnegative times as the difference of two nondecreasing real functions. The proof must construct the genuine original process-path decomposition from its Lévy-Itô jump representation or an equivalent process-law theorem, including infinite-activity finite-variation jumps and time-zero consistency. No bounded-variation or monotone-path conclusion is assumed.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, sufficiency via drift plus absolute sum of Poisson jumps.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyFiniteVariationMonotoneJordanRepresentationV1
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
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    ∀ᵐ ω ∂P,
      ∃ (p q : ℝ≥0 → ℝ), Monotone p ∧ Monotone q ∧
        ∀ t : ℝ≥0, X t ω = p t - q t := by
  sorry
