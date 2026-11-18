-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_6
-- name    : Kyprianou.Ch09.stageC_result_9_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:25:21.720097+00:00
-- url     : https://prove2.me/theorems/5473fde9-0e51-4743-a372-e37d64d79e64
-- title:
--   Result 9.6: Novikov–Shiryaev power reward and stopping
-- statement:
--   Result 9.6. Model and parameter assumptions: n∈{1,2,…}, q>0 as in (9.14), X any Lévy process with ∫_(1,∞)u^n Π(du)<∞; Y=overline X_(e_q), Appell Q_n for Y. Quantifiers and stopping-time domain: Every n≥1, all x∈ℝ and the full stopping class T. Mathematical assertion: Q_n finite coefficients; x*_n∈[0,∞) is largest root of Q_n=0; τ*_n=inf{t≥0:X_t≥x*_n} optimal; v_n(x)=E_x[Q_n(overline X_(e_q)) 1_{overline X_(e_q)≥x*_n}]. Endpoint and source qualification: Keep full original optimality/value claim including x*_n=0; repaired root/sign facts are sourced from I-01 with proof still required. q=0 extension on p.254 needs limsup X_t<∞ and (n+1)st jump moment separately. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.6; original PDF pp. [258]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceAppell
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_6 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e),
    ∃ Q : ℕ → Polynomial ℝ,
      B1.AppellPolynomialFamily (P.prod ν)
        (B1.expMaximum X e) n Q ∧
      ∃ z : ℝ, 0 ≤ z ∧ (Q n).eval z = 0 ∧
        (∀ y : ℝ, 0 ≤ y → (Q n).eval y = 0 → y ≤ z) ∧
        ∀ x : ℝ,
          let τ := fun ω => B1.firstWeakAbove
            (fun t ξ => x + X t ξ) z ω
          B1.AdmissibleStop F τ ∧
          B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0) =
            B1.appellCandidateValue P ν X e (Q n) z x ∧
          B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0) =
            (∫ ω, B1.stoppedGain X (B1.powerGain n) q x
              (fun _ => 0) τ ω ∂P) := by
  sorry

end Kyprianou.Ch09
