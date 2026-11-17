-- Prove2me | Theorems.Thm_IntervalToDynamic_Supplement_theorem_9
-- name    : IntervalToDynamic.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:42:09.383823+00:00
-- url     : https://prove2.me/theorems/62e46187-5cea-4d4c-9d7e-b1cf55da1443
-- title:
--   Theorem 9 — algorithm realizability
-- statement:
--   Fix $d,k\ge1$, the ball $\mathcal Y=B(D_{\mathcal Y}/2)$, a positive Lipschitz bound $G_h$, and positive exp-concavity and strong-convexity coefficients. There are positive constants and fixed nonnegative integer powers, all independent of the horizon and losses, such that for every horizon Algorithms 3–4 exist in each of the three modes and satisfy polynomial interval regret simultaneously on every interval against every $q\in\mathcal P_{k-1}(I;\mathcal Y)$ at rates
--   $$
--   C_{\rm cvx}(1+\log T)^{p_{\rm cvx}}\sqrt{|I|},\qquad
--   C_{\rm exp}(1+\log T)^{p_{\rm exp}}d(1+\log|I|),\qquad
--   C_{\rm sc}(1+\log T)^{p_{\rm sc}}(1+\log|I|).
--   $$
--   The loss classes are differentiable convex $G_h$-Lipschitz losses, with the corresponding exp-concavity or strong-convexity property in the curved modes.
--
--   The algorithm objects implement the exact dyadic cover, polynomial coefficient domains, OGD/ONS base updates, priors, mode-specific aggregation probabilities and weight recurrences printed in Algorithms 3–4.
--
--   Differences from the source:
--   - encoding: $\widetilde O_k$ rates required by Theorem 7 → positive constants and fixed powers of $1+\log T$, quantified before the horizon and multiplied by the displayed $\sqrt{|I|}$ or $1+\log|I|$ factors; reason: this retains the logarithmic factors in $T$ that the paper hides while preserving the displayed $\log|I|$ dependence
--   - encoding: Algorithms 3 and 4 given as pseudocode → a structure whose fields are the exact geometric-cover, basis, feasibility, projected base-update, active aggregation and weight-update equations, together with a history-map algorithm agreeing with the aggregate decisions; reason: this makes the named algorithms mathematical data rather than an informal label
--   - encoding: differentiable losses and observed gradients on the closed ball → `DifferentiableOn` together with a domain-relative gradient oracle satisfying `HasGradientWithinAt`; reason: this represents the paper's gradient observations without adding ambient differentiability at boundary points
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Theorem 9, p.42 (PDF p.44); Algorithms 3–4 and proof, pp.43–50 (PDF pp.45–52)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Algorithms34
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace IntervalToDynamic.Supplement

/-- Theorem 9 (algorithm realizability), Wang--Zhao--Zhou,
*On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423,
Theorem 9, p.42 (PDF p.44), with Algorithms 3--4 on pp.46 and 49.

One theorem covers all three branches. `Algorithms34` records the printed dyadic cover,
polynomial lifting and mode-specific base/meta recurrences; the conclusions are simultaneous on
every interval and against every polynomial comparator. The constants hidden by `Õ_k` are fixed
before the horizon and loss sequence, while explicit powers of `1 + log T` retain the logarithmic
factors in the paper's `Õ_k` notation. -/
theorem theorem_9 {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k)
    (DY Gh alpha lam : ℝ) (hDY : 0 < DY) (hGh : 0 < Gh)
    (halpha : 0 < alpha) (hlam : 0 < lam) :
    ∃ Cconv Cexp Cstrong : ℝ,
    ∃ pconv pexp pstrong : ℕ,
      0 < Cconv ∧ 0 < Cexp ∧ 0 < Cstrong ∧
      ∀ T : ℕ, 1 ≤ T →
      (∃ S : Algorithms34 .convex T d k DY Gh,
        HasPolynomialIntervalRegret S.A
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2))
          (fun h => DifferentiableOn ℝ h (Metric.closedBall 0 (DY / 2)) ∧
            ConvexOn ℝ (Metric.closedBall 0 (DY / 2)) h ∧
            ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
              ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
                |h y - h z| ≤ Gh * ‖y - z‖)
          T k (fun n => Cconv * (1 + Real.log T) ^ pconv * Real.sqrt n)) ∧
      (∃ S : Algorithms34 (.expConcave alpha) T d k DY Gh,
        HasPolynomialIntervalRegret S.A
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2))
          (fun h => DifferentiableOn ℝ h (Metric.closedBall 0 (DY / 2)) ∧
            ConvexOn ℝ (Metric.closedBall 0 (DY / 2)) h ∧
            (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
              ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
                |h y - h z| ≤ Gh * ‖y - z‖) ∧
            LogRegretOCO.ONS.IsExpConcaveOn alpha (Metric.closedBall 0 (DY / 2)) h)
          T k (fun n => Cexp * (1 + Real.log T) ^ pexp * d * (1 + Real.log n))) ∧
      (∃ S : Algorithms34 (.stronglyConvex lam) T d k DY Gh,
        HasPolynomialIntervalRegret S.A
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2))
          (fun h => DifferentiableOn ℝ h (Metric.closedBall 0 (DY / 2)) ∧
            ConvexOn ℝ (Metric.closedBall 0 (DY / 2)) h ∧
            (∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
              ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (DY / 2),
                |h y - h z| ≤ Gh * ‖y - z‖) ∧
            StrongConvexOn (Metric.closedBall 0 (DY / 2)) lam h)
          T k (fun n => Cstrong * (1 + Real.log T) ^ pstrong *
            (1 + Real.log n))) := by sorry

end IntervalToDynamic.Supplement
