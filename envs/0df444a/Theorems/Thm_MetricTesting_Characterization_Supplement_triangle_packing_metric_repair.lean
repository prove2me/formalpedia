-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_triangle_packing_metric_repair
-- name    : MetricTesting.Characterization.Supplement.triangle_packing_metric_repair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:17.224745+00:00
-- url     : https://prove2.me/theorems/09ac590f-eb38-439b-bb8e-9af51c0eb4c5
-- title:
--   Proposition 5.17 — Triangle packing bounds metric repair
-- statement:
--   Let $C>1$, $n\ge3$, and $D\in[1,C]^{\binom{[n]}2}$. Let $\nu(D)$ be the maximum number of edge-disjoint violating triangles and $M_C=\prod_{r=4}^{\lceil C\rceil}(r+1)$. Then
--
--   $$\frac{2\nu(D)}{n^2}\le\operatorname{dist}_n(D,\mathcal M_n)
--   =\operatorname{dist}_n(D,\mathcal M_n[1,C])\le\frac{6M_C\nu(D)}{n^2}.$$
--
--   The repair distances use normalized exact Hamming discrepancies, and $M_C$ is one when $1<C\le3$.
--
--   This comparison relates the triangle-packing parameter directly to metric repair with the exact source constants.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 24, Proposition 5.17 (PDF p. 25); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem triangle_packing_metric_repair (C : ℝ) (hC : 1 < C) (n : ℕ) (hn : 3 ≤ n)
    (D : Array (BoundedValues C) n) :
    2 * (packingNumber (boundedMetric C hC) D : ℝ) / (n : ℝ)^2 ≤ crossDistance positiveMetric D ∧
    crossDistance positiveMetric D = repairDistance (boundedMetric C hC) D ∧
    repairDistance (boundedMetric C hC) D ≤
      6 * (completionFactor C : ℝ) * (packingNumber (boundedMetric C hC) D : ℝ) / (n : ℝ)^2 := by sorry

end MetricTesting.Characterization.Supplement
