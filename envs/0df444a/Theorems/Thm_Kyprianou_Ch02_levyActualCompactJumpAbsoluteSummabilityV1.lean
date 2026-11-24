-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyActualCompactJumpAbsoluteSummabilityV1
-- name    : Kyprianou.Ch02.levyActualCompactJumpAbsoluteSummabilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:03:06.890816+00:00
-- url     : https://prove2.me/theorems/9c01393a-613b-4038-81e2-048f9e0d68c0
-- title:
--   Absolute summability of actual positive-time Levy jumps from finite truncated first moment
-- statement:
--   For the exact original real Levy process prescribed by its Levy-Khintchine characteristic triplet, a finite truncated absolute Levy measure first moment ensures that almost every trajectory has absolutely summable actual positive-time jumps on every compact interval. Count the actual left-limit discontinuities; do not assume bounded variation or a preconstructed jump series. This allows arbitrary nonzero Gaussian coefficient because Brownian paths are continuous.
-- source:
--   Kyprianou (2006) Chapter 2 Lemma 2.12, finite-variation form of the Lévy-Ito decomposition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyActualCompactJumpAbsoluteSummabilityV1
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
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure →
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
        |X (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|) := by
  sorry
