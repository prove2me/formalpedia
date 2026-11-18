-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_4
-- name    : Kyprianou.Ch09.stageC_result_9_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:24:41.898959+00:00
-- url     : https://prove2.me/theorems/b8008573-d5d5-4781-b6eb-dfad0f350d2b
-- title:
--   Result 9.4: McKean convexity and smooth fit
-- statement:
--   Result 9.4. Model and parameter assumptions: McKean setting (9.3), with q=0 requiring X_t→+∞, and the regularity criterion for the origin from below. Quantifiers and stopping-time domain: Every y>0 for convexity, every admissible model with x* from Theorem 9.2. Mathematical assertion: y↦v(log y) is convex; continuous fit at x*; v′(x*+)=−e^(x*)+K P(underline X_(e_q)=0); smooth fit iff 0 is regular for (−∞,0). Endpoint and source qualification: Same as printed, with the q=0 drift direction inherited accurately from Theorem 9.2. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.4; original PDF pp. [253]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_4 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q K : ℝ)
    (hX : B1.SourceModel P X F)
    (hK : 0 < K) (hDomain : B1.McKeanDomain P ν X q e),
    let m := B1.killedInfimumMoment P ν X e
    let z := Real.log (K * m)
    let v := fun x : ℝ =>
      B1.optionValue P F X (B1.putGain K) q x (fun _ => 0)
    0 < m ∧ ConvexOn ℝ (Set.Ioi 0) (fun y => v (Real.log y)) ∧
      ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Ici z) z =
        -Real.exp z +
          K * ((P.prod ν)
            {pair : Ω × E | B1.pathInfAt X (e pair.2) pair.1 = 0}).toReal ∧
      (B1.SmoothFitAt v z ↔ B1.RegularBelow P X) := by
  sorry

end Kyprianou.Ch09
