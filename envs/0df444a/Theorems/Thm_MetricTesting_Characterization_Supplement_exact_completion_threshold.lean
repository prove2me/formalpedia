-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_exact_completion_threshold
-- name    : MetricTesting.Characterization.Supplement.exact_completion_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:04.58005+00:00
-- url     : https://prove2.me/theorems/1229d269-6f6c-44cc-bcef-ee9b75667b19
-- title:
--   Proposition 5.9 — Exact completion threshold at C = 3
-- statement:
--   Let $C>1$, and write $\Gamma_C$ for the published completion modulus of the metric predicate on $[1,C]$. If $C\le3$, every locally consistent partial array has an exact bounded metric completion, and
--
--   $$\Gamma_C(\theta)=0\qquad(\theta\ge0).$$
--
--   If $C>3$, some locally consistent partial array has no exact completion, and
--
--   $$\Gamma_C(\theta)\ge\frac{\theta}{1+8\theta}\qquad(\theta>0).$$
--
--   The result separates the exact-completion threshold at three from the all-complete-inputs-metric threshold at two. Local consistency tests only fully specified triples.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 21, Proposition 5.9 (PDF p. 22); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem exact_completion_threshold (C : ℝ) (hC : 1 < C) :
    (C ≤ 3 →
      (∀ n : ℕ, 1 ≤ n → ∀ A : PartialArray (BoundedValues C) n,
        LocallyConsistent (boundedMetric C hC) A → ExactCompletion (boundedMetric C hC) A) ∧
      (∀ θ : ℝ, 0 ≤ θ → completionModulus (boundedMetric C hC) θ = 0)) ∧
    (3 < C →
      (∃ n : ℕ, 3 ≤ n ∧ ∃ A : PartialArray (BoundedValues C) n,
        LocallyConsistent (boundedMetric C hC) A ∧ ¬ ExactCompletion (boundedMetric C hC) A) ∧
      (∀ θ : ℝ, 0 < θ → θ / (1+8*θ) ≤ completionModulus (boundedMetric C hC) θ)) := by sorry

end MetricTesting.Characterization.Supplement
