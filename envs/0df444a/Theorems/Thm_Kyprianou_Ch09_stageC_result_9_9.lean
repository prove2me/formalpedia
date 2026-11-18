-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_9
-- name    : Kyprianou.Ch09.stageC_result_9_9
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:41:38.610897+00:00
-- url     : https://prove2.me/theorems/d25e2dab-1c07-496b-aef6-83dda96f6514
-- title:
--   Result 9.9: Appell first-passage fluctuation identity
-- statement:
--   Result 9.9. Model and parameter assumptions: n≥1, q>0, ∫_(1,∞)u^n Π(du)<∞, Lévy process X, independent e_q, T_a⁺=inf{t≥0:X_t≥a}. Quantifiers and stopping-time domain: Every a>0 and x∈ℝ, including overshoot events. Mathematical assertion: E_x[e^(−qT_a⁺) (X_(T_a⁺))^n 1_{T_a⁺<∞}]=E_x[Q_n(overline X_(e_q))1_{overline X_(e_q)≥a}]. Endpoint and source qualification: Same as printed, preserving weak passage and q>0 memorylessness. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.9; original PDF pp. [259]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceAppell
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_9 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (Q : ℕ → Polynomial ℝ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e)
    (hQ : B1.AppellPolynomialFamily (P.prod ν)
      (B1.expMaximum X e) n Q),
    ∀ a x : ℝ, 0 < a →
      (∫ ω, match B1.firstWeakAbove
        (fun t ξ => x + X t ξ) a ω with
        | ⊤ => (0 : ℝ)
        | (t : ℝ≥0) =>
          Real.exp (-q * (t : ℝ)) * (x + X t ω) ^ n ∂P) =
      B1.appellCandidateValue P ν X e (Q n) a x := by
  sorry

end Kyprianou.Ch09
