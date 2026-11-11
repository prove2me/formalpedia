-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_3_4
-- name    : MulticalibrationERM.Oracle.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:35.905582+00:00
-- url     : https://prove2.me/theorems/2bf82269-1151-4ffb-8c31-b0567bf3f3a3
-- title:
--   Lemma 3.4 — the minimax forecast: adjacent support, O(m) time, nonpositive virtual payoff
-- statement:
--   There is an absolute constant $C$ such that for every $K\ge1$ and every $a\in[-1,1]^\Lambda$, the minimax forecast $P=\mathrm{Minimax}(a)$ is a distribution on $\Lambda$ with adjacent support, computed with at most $C\,m$ elementary operations, and with $\mu=\sum_vP(v)\,v$,
--   $$(\mu-y)\sum_{v\in\Lambda}P(v)\,a_v\le0\qquad\text{for every }y\in[0,1].$$
--
--   Differences from the source:
--   - encoding: computable in O(m) time → the operation count minimaxOps of the stated procedure (unit-cost model) is at most C·m for an absolute C; reason: a running time needs a cost model; the count follows the procedure step by step
--   - encoding: grid values v ∈ Λ → grid indices i ∈ Fin (K + 1) with value i/K; reason: relabelling
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 17, Lemma 3.4

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_Forecast

namespace MulticalibrationERM.Oracle

/-- Lemma 3.4 (p. 17): for `a ∈ [−1, 1]^Λ` the minimax forecast `P = Minimax(a)` is a
distribution on the grid with adjacent support, computed with `O(m)` operations, and with
mean `µ` satisfies `(µ − y) ∑_v P(v) a_v ≤ 0` for every `y ∈ [0, 1]`. -/
theorem lemma_3_4 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ), 1 ≤ K → ∀ a : Fin (K + 1) → ℝ, (∀ v, a v ∈ Set.Icc (-1 : ℝ) 1) →
      IsDist (minimax K 0 K a) ∧ AdjSupport (minimax K 0 K a) ∧
      (minimaxOps K 0 K a : ℝ) ≤ C * (K + 1) ∧
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        (gridMean (minimax K 0 K a) - y) * ∑ v, minimax K 0 K a v * a v ≤ 0 := by sorry

end MulticalibrationERM.Oracle
