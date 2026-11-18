-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_10
-- name    : Kyprianou.Ch09.stageC_result_9_10
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:42:18.514397+00:00
-- url     : https://prove2.me/theorems/b5b3247d-f820-4d3c-a1c4-0a3a77b795dd
-- title:
--   Result 9.10: Largest nonnegative Appell root and sign
-- statement:
--   Result 9.10. Model and parameter assumptions: n≥1, q>0, X Lévy with ∫_(1,∞)u^n Π(du)<∞, Y=overline X_(e_q). Quantifiers and stopping-time domain: Every such X and n, including X_t=−t, X_t=d t and zero Lévy measure. Mathematical assertion: Q_n has a largest nonnegative root x*_n; Q_n≤0 on [0,x*_n], Q_n>0 on (x*_n,∞), Q_n nondecreasing for x≥x*_n. Strict positivity of x*_n requires P(Y>0)>0; Q_n(0)<0 requires a further property, not assumed. General endpoint Q_n(0)≤0 and induction remain to be proved, especially when P(Y=0)=0. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.10; original PDF pp. [259]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceAppell
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_10 :
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
    ∃ z : ℝ, 0 ≤ z ∧ (Q n).eval z = 0 ∧
      (∀ x : ℝ, 0 ≤ x → (Q n).eval x = 0 → x ≤ z) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ z → (Q n).eval x ≤ 0) ∧
      (∀ x : ℝ, z < x → 0 < (Q n).eval x) ∧
      MonotoneOn (fun x : ℝ => (Q n).eval x) (Set.Ici z) := by
  sorry

end Kyprianou.Ch09
