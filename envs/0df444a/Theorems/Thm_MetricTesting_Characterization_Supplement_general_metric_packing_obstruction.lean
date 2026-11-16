-- Prove2me | Theorems.Thm_MetricTesting_Characterization_Supplement_general_metric_packing_obstruction
-- name    : MetricTesting.Characterization.Supplement.general_metric_packing_obstruction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:22:47.585493+00:00
-- url     : https://prove2.me/theorems/dec40aaf-e76b-479b-b124-6b8280233bbe
-- title:
--   Theorem 4.11 — Packing obstruction for general metrics
-- statement:
--   Let $C>2$ and $\beta=1/20$. For each of the bounded metric family on $[1,C]$, the positive metric family on $(0,\infty)$, and the nonnegative pseudometric family on $[0,\infty)$, there is an operational packing-obstruction sequence and
--
--   $$\Delta(\beta)=0,\qquad \rho(\epsilon)=0\quad(0<\epsilon<1/10).$$
--
--   None of the three families is one-sided constant-query testable. Here $\Delta$ is the published packing modulus and $\rho$ the removal modulus, using $2/n^2$ discrepancy normalization and strict distance $>\epsilon$.
--
--   The statement distinguishes failure of amplification from completion stability and retains both exact zero-modulus claims in every ambient domain.
--
--   Differences from the source:
--   - encoding: symmetric zero-diagonal arrays on [n] and local validity → the published unordered-pair Array on Fin n, with inherited local-family conventions; reason: relabeling preserves every input, target, discrepancy and query
--   - encoding: packing obstruction → explicit orders tending to infinity, positive quadratic packing density and violation density tending to zero; reason: the operational sequence from Corollary 3.12 is stated rather than defining obstruction as nonremovability
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 17, Theorem 4.11 (PDF p. 18); SHA-256 3e49396763fea65b4a7151b904f1cba07f70024d5c851dce84339c98c8148be9

import Mathlib
import Definitions.Def_MetricTesting_Characterization_Supplement_completion
import Definitions.Def_MetricTesting_Characterization_decision_tree

set_option autoImplicit false
noncomputable section

namespace MetricTesting.Characterization.Supplement

theorem general_metric_packing_obstruction (C : ℝ) (hC : 2 < C) :
    ∀ F ∈ ({boundedMetric C (by linarith), positiveMetric, pseudoMetric} : Set LocalData),
      PackingObstruction F ∧ packingModulus F (1/20) = 0 ∧
      (∀ ε : ℝ, 0 < ε → ε < 1/10 → removalModulus F ε = 0) ∧
      ¬ OneSidedTestable F := by sorry

end MetricTesting.Characterization.Supplement
