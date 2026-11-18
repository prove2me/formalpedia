-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_part_exercise_9_1_i
-- name    : Kyprianou.Ch09.stageC_part_exercise_9_1_i
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:47:42.424841+00:00
-- url     : https://prove2.me/theorems/8711e2bb-828d-47c7-a160-b177395d0333
-- title:
--   Exercise 9.1.i: Discounted upward first-passage identity
-- statement:
--   Exercise 9.1.i (Discounted upward first-passage identity). Assumptions: X any Lévy process; q>0 OR q=0 AND X_t→−∞ a.s. (distinct from Theorem 9.2), T all ℱ-stopping times; supremum overline X_(e_q). Quantification: All initial x∈ℝ and a>0 for (i); all x for (ii) and fit test (iii). Required mathematical conclusion in this subpart: Prove discounted upcrossing identity using exponential-time supremum.. The original chapter exercise specifies the formulas and companion cases: (i) E_x[e^(−qT_a⁺)(1−e^(−X_(T_a⁺)))1_{T_a⁺<∞}]=E_x[(1−e^(−overline X_(e_q))/E[e^(−overline X_(e_q))])1_{overline X_(e_q)≥a}]; (ii) x* solves e^(−x*)=E[e^(−overline X_(e_q))], value from (i) with a=x*, τ*=T_(x*)⁺; (iii) smooth fit iff 0 upward regular, otherwise continuous fit.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem exercise:9.1.i; original PDF pp. [277]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceMcKean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_part_exercise_9_1_i :
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
    ∀ a x : ℝ, 0 < a →
      (∫ ω, match B1.firstWeakAbove
         (fun t ξ => x + X t ξ) a ω with
        | ⊤ => (0 : ℝ)
        | (t : ℝ≥0) =>
          Real.exp (-q * (t : ℝ)) *
            (1 - Real.exp (-(x + X t ω))) ∂P) =
      (∫ pair : Ω × E,
        if a ≤ x + B1.pathSupAt X (e pair.2) pair.1 then
          1 - Real.exp
            (-(x + B1.pathSupAt X (e pair.2) pair.1)) / m
        else 0 ∂(P.prod ν)) := by
  sorry

end Kyprianou.Ch09
