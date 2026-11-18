-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_1_iii
-- name    : Kyprianou.Ch09.stageC_part_exercise_9_1_iii
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:49:07.149273+00:00
-- url     : https://prove2.me/theorems/29ec7d81-51ef-41ad-9677-1eeb35681884
-- title:
--   Exercise 9.1.iii: Regularity and smooth fit of exponential reward
-- statement:
--   Exercise 9.1.iii (Regularity and smooth fit of exponential reward). Assumptions: X any Lévy process; q>0 OR q=0 AND X_t→−∞ a.s. (distinct from Theorem 9.2), T all ℱ-stopping times; supremum overline X_(e_q). Quantification: All initial x∈ℝ and a>0 for (i); all x for (ii) and fit test (iii). Required mathematical conclusion in this subpart: Show smooth fit iff regularity for (0,infinity), with continuous fit otherwise.. The original chapter exercise specifies the formulas and companion cases: (i) E_x[e^(−qT_a⁺)(1−e^(−X_(T_a⁺)))1_{T_a⁺<∞}]=E_x[(1−e^(−overline X_(e_q))/E[e^(−overline X_(e_q))])1_{overline X_(e_q)≥a}]; (ii) x* solves e^(−x*)=E[e^(−overline X_(e_q))], value from (i) with a=x*, τ*=T_(x*)⁺; (iii) smooth fit iff 0 upward regular, otherwise continuous fit.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem exercise:9.1.iii; original PDF pp. [277]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_part_exercise_9_1_iii :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (q : ℝ)
    (hX : B1.SourceModel P X F)
    (hDomain : B1.Exercise91Domain P ν X q e),
    let m := ∫ pair : Ω × E,
      Real.exp (-B1.pathSupAt X (e pair.2) pair.1) ∂(P.prod ν)
    let z := -Real.log m
    let v := fun x : ℝ =>
      B1.optionValue P F X B1.exercise91Gain q x (fun _ => 0)
    0 < m ∧ ContinuousAt v z ∧
      (B1.SmoothFitAt v z ↔ B1.RegularAbove P X) := by
  sorry

end Kyprianou.Ch09
