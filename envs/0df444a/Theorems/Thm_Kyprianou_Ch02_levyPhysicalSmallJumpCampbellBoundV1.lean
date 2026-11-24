-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyPhysicalSmallJumpCampbellBoundV1
-- name    : Kyprianou.Ch02.levyPhysicalSmallJumpCampbellBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:58:11.883445+00:00
-- url     : https://prove2.me/theorems/b8fdd5c1-03b1-41d3-a744-3b2d37743073
-- title:
--   Original Lévy process physical small-jump Campbell intensity bound, integer clocks
-- statement:
--   For every original real Levy process carrying the specified characteristic triplet, the actual chronological positive-time jumps of absolute size at most one define an almost everywhere measurable extended nonnegative absolute-mass random variable on each integer horizon. Its expected mass is bounded by time times the first truncated jump-moment integral of the source Levy measure, whether or not that moment is finite. The theorem must use the actual original process and identify the correct jump-intensity compensation from its characteristic exponent; it may not assume finite-variation paths, an auxiliary Poisson realization, or absolute summability in advance.
-- source:
--   Kyprianou (2006), Chapter 2: large-jump finite-activity property and small-jump first-moment compensator in Lemma 2.12.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyPhysicalSmallJumpCampbellBoundV1
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
    ∀ n : ℕ,
      AEMeasurable (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
           ENNReal.ofReal (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
          (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure) := by
  sorry
