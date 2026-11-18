-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_12
-- name    : Kyprianou.Ch09.stageC_result_9_12
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:43:29.969778+00:00
-- url     : https://prove2.me/theorems/5c9fdcb1-913d-429d-898b-f113f1635e2a
-- title:
--   Result 9.12: Reflected Russian-option continuous and non-smooth fit
-- statement:
--   Result 9.12. Model and parameter assumptions: All of Theorem 9.11 with q<d (hence x*>0). Quantifiers and stopping-time domain: Every x≥0 and the unique positive threshold x*. Mathematical assertion: v convex and continuously fitted at x*, with v′(x*−)=v′(x*+)−(q/d)e^(x*); no smooth fit. Endpoint and source qualification: Same as printed; clarify that q=d gives f(0+)=0 and is outside this corollary. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.12; original PDF pp. [265]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceReflected
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_12 :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (q : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hDiffuse : B1.IsAtomlessPositiveJumpMeasure jumpMeasure)
    (hq : ψ 1 < q) (hq0 : 0 < q)
    (hsmall : q < d) (hScale : B1.IsScale ψ q W),
    let z := B1.russianThreshold q W
    let v := fun x : ℝ => Real.exp x * B1.scaleZ q W (z - x)
    0 < z ∧ ConvexOn ℝ (Set.Ici 0) v ∧
      ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Iic z) z =
        derivWithin v (Set.Ici z) z - q / d * Real.exp z ∧
      ¬ B1.SmoothFitAt v z := by
  sorry

end Kyprianou.Ch09
