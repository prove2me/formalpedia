-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_metric_completion_cycle_criterion
-- name    : MetricTesting.Characterization.Supplement.metric_completion_cycle_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:36.228204+00:00
-- url     : https://prove2.me/theorems/5bbec722-6975-406e-bf20-28009cf9b019
-- title:
--   Lemma 5.8 — Exact completion and nonmetric cycles
-- statement:
--   Let $C>1$, and let $A$ be a partial symmetric zero-diagonal array on $n$ labels with specified entries in $[1,C]$. Write $G_A$ for its graph of specified pairs. Then
--
--   $$A\text{ has an exact metric completion in }[1,C]\quad\Longleftrightarrow\quad G_A\text{ has no nonmetric simple cycle}.$$
--
--   A nonmetric cycle has an edge strictly longer than the sum of its remaining edges. Exact completion preserves every specified entry. There is no local-consistency or connectivity assumption.
--
--   This criterion identifies the deterministic obstruction to preserving all specified distances, for arbitrary real weights in the stated range.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 21, Lemma 5.8 (PDF p. 22); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem metric_completion_cycle_criterion (C : ℝ) (hC : 1 < C) (n : ℕ) (hn : 1 ≤ n)
    (A : PartialArray (BoundedValues C) n) :
    ExactCompletion (boundedMetric C hC) A ↔
      ∀ r : ℕ, ∀ E : Finset (Edge n), ¬ NonmetricCycle A r E := by sorry

end MetricTesting.Characterization.Supplement
