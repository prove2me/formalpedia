-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_2_4
-- name    : OptimalTraceDistance.Estimation.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:50.591273+00:00
-- url     : https://prove2.me/theorems/30b7e959-bad1-4bf8-a533-11924121a0fa
-- title:
--   Lemma 2.4 — trace error under low-rank perturbations
-- statement:
--   There is a universal $C>0$ such that for every $K\ge2$, $s>0$ and equal-sized Hermitian matrices $U,V$ with $\|U\|_\infty,\|V\|_\infty\le s$,
--   $$|E_{K,s}(U)-E_{K,s}(V)|\le\frac{Cs}{K}\operatorname{rank}(U-V).$$
--   Here $E_{K,s}(U)=\operatorname{tr}(|U|-q_{K,s}(U))$ for the fixed Jackson family. No rank or invertibility promise is imposed on $U$ or $V$.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 2.4, p. 7.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_2_4 : ∃ C : ℝ, 0 < C ∧ ∀ (d K : ℕ), 0 < d → 2 ≤ K →
  ∀ s : ℝ, 0 < s → ∀ U V : Mat d, U.IsHermitian → V.IsHermitian →
    opNorm U ≤ s → opNorm V ≤ s →
    |traceError K s U - traceError K s V| ≤ C*s/(K : ℝ) * (U-V).rank := by sorry

end OptimalTraceDistance.Estimation
