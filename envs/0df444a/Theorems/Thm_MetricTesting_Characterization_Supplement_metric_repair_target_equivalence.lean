-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_metric_repair_target_equivalence
-- name    : MetricTesting.Characterization.Supplement.metric_repair_target_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:26:39.041995+00:00
-- url     : https://prove2.me/theorems/d2dd53cf-0b30-4f1f-9136-9b81aea71685
-- title:
--   Lemma 5.16 — Equality of metric repair targets
-- statement:
--   Let $C>1$ and let $D$ be any symmetric zero-diagonal array with off-diagonal entries in $[1,C]$. Write $\mathcal M_n[1,C]$ for bounded positive metrics, $\mathcal M_n$ for arbitrary positive metrics, and $\overline{\mathcal M}_n$ for nonnegative pseudometrics. Then
--
--   $$\operatorname{dist}_n(D,\mathcal M_n[1,C])=
--   \operatorname{dist}_n(D,\mathcal M_n)=\operatorname{dist}_n(D,\overline{\mathcal M}_n).$$
--
--   Distances count unequal unordered pairs with factor $2/n^2$, even when a target value lies outside the input range. The bounded distance uses the published repair-distance definition; the other distances explicitly compare coerced nonnegative real entries.
--
--   The equality transfers testing lower bounds between repair classes without restricting the original real-valued input model.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: distances to positive or nonnegative targets outside the input range → cross-value minimization compares NNReal coercions; the bounded term is the published repairDistance; reason: the equality is a theorem, not a definitional identification; all these target classes are nonempty
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 24, Lemma 5.16 (PDF p. 25); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem metric_repair_target_equivalence (C : ℝ) (hC : 1 < C) (n : ℕ) (hn : 1 ≤ n)
    (D : Array (BoundedValues C) n) :
    repairDistance (boundedMetric C hC) D = crossDistance positiveMetric D ∧
      crossDistance positiveMetric D = crossDistance pseudoMetric D := by sorry

end MetricTesting.Characterization.Supplement
