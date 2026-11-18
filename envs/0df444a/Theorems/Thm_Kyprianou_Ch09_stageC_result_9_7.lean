-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_7
-- name    : Kyprianou.Ch09.stageC_result_9_7
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:26:10.531589+00:00
-- url     : https://prove2.me/theorems/2e31c5aa-268d-4ee6-8207-41f87b135412
-- title:
--   Result 9.7: Novikov–Shiryaev fit and derivative jump
-- statement:
--   Result 9.7. Model and parameter assumptions: Theorem 9.6 hypotheses and repaired largest nonnegative Appell threshold x*_n; q>0. Quantifiers and stopping-time domain: Every integer n≥1, including x*_n=0 and processes with P(Y=0)=1. Mathematical assertion: v_n convex and continuously fitted, with printed one-sided derivative formula. Smooth fit iff Q′_n(x*_n)·P(Y=0)=0. The upward-regularity iff follows only when Q′_n(x*_n)≠0; include nonregular degenerate cases where Q′_n(x*_n)=0. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.7; original PDF pp. [258]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceAppell
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_7 :
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (e : E → WithTop ℝ≥0)
    (jumpMeasure : Measure ℝ) (q : ℝ) (n : ℕ)
    (Q : ℕ → Polynomial ℝ) (z : ℝ)
    (hX : B1.SourceModel P X F)
    (hJump : B1.IsJumpMeasureFor P X jumpMeasure)
    (hn : 1 ≤ n) (hq : 0 < q)
    (hmoment : B1.PositiveJumpMoment jumpMeasure n)
    (hExp : B1.ExponentialHorizon ν q e)
    (hQ : B1.AppellPolynomialFamily (P.prod ν)
      (B1.expMaximum X e) n Q)
    (hRoot : 0 ≤ z ∧ (Q n).eval z = 0 ∧
      ∀ y : ℝ, 0 ≤ y → (Q n).eval y = 0 → y ≤ z),
    let v := fun x : ℝ =>
      B1.optionValue P F X (B1.powerGain n) q x (fun _ => 0)
    let atom := ((P.prod ν)
      {pair : Ω × E | B1.expMaximum X e pair = 0}).toReal
    ConvexOn ℝ (Set.univ : Set ℝ) v ∧ ContinuousAt v z ∧
      DifferentiableWithinAt ℝ v (Set.Iic z) z ∧
      DifferentiableWithinAt ℝ v (Set.Ici z) z ∧
      derivWithin v (Set.Iic z) z =
        derivWithin v (Set.Ici z) z -
        (Q n).derivative.eval z * atom ∧
      (B1.SmoothFitAt v z ↔ (Q n).derivative.eval z * atom = 0) ∧
      ((Q n).derivative.eval z ≠ 0 →
        (B1.SmoothFitAt v z ↔ B1.RegularAbove P X)) := by
  sorry

end Kyprianou.Ch09
