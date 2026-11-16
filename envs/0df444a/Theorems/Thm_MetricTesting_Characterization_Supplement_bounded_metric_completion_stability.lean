-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_bounded_metric_completion_stability
-- name    : MetricTesting.Characterization.Supplement.bounded_metric_completion_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:25:27.948837+00:00
-- url     : https://prove2.me/theorems/5920dec7-02a4-4b3e-a58f-ed84ec57fa9d
-- title:
--   Theorem 5.13 — Bounded aspect-ratio completion stability
-- statement:
--   Fix a real $C>1$ and put $M_C=\prod_{r=4}^{\lceil C\rceil}(r+1)$, with empty product one. Every locally consistent partial array in $[1,C]$ with $h$ holes becomes exactly metrically completable in $[1,C]$ after deleting a set of at most $(M_C-1)h$ specified edges. Consequently,
--
--   $$\Gamma_C(\theta)\le\min\{1,2(M_C-1)\theta\}\qquad(\theta\ge0).$$
--
--   For every fixed $C>3$, there are positive $a_C,b_C,t_C$ such that
--
--   $$a_C\theta\le\Gamma_C(\theta)\le b_C\theta\qquad(0<\theta\le t_C).$$
--
--   Thus $\Gamma_C(\theta)=\Theta_C(\theta)$ as $\theta\downarrow0$. All three conclusions are retained, including the explicit product factor and both sides of the small-hole asymptotic order.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: Γ(θ)=Θ_C(θ) as θ decreases to zero → positive a,b,t with aθ ≤ Γ(θ) ≤ bθ for 0<θ≤t; reason: the two-sided asymptotic claim is unchanged; the exact deletion factor and modulus bound are also retained
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 23, Theorem 5.13 (PDF p. 24); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem bounded_metric_completion_stability (C : ℝ) (hC : 1 < C) :
    (∀ n : ℕ, 1 ≤ n → ∀ A : PartialArray (BoundedValues C) n,
      LocallyConsistent (boundedMetric C hC) A →
      ∃ S : Finset (Edge n), S ⊆ Specified A ∧
        S.card ≤ (completionFactor C - 1) * (Holes A).card ∧
        ExactCompletion (boundedMetric C hC) (deleteEdges A S)) ∧
    (∀ θ : ℝ, 0 ≤ θ → completionModulus (boundedMetric C hC) θ ≤
      min 1 (2 * ((completionFactor C : ℝ) - 1) * θ)) ∧
    (3 < C → ∃ a b t : ℝ, 0 < a ∧ 0 < b ∧ 0 < t ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ t →
        a * θ ≤ completionModulus (boundedMetric C hC) θ ∧
        completionModulus (boundedMetric C hC) θ ≤ b * θ) := by sorry

end MetricTesting.Characterization.Supplement
