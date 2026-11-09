-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_A_1
-- name    : OptimalTraceDistance.Estimation.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:37.4802+00:00
-- url     : https://prove2.me/theorems/0f3408c2-3225-48bd-b920-1e8d60345765
-- title:
--   Lemma A.1 — trace error under congruence
-- statement:
--   Let $K\ge2$, $s>0$, let $U$ be Hermitian with $\|U\|_\infty\le s$, and let $0\prec\Lambda\preceq I$. Then
--   $$|E_{K,s}(\Lambda U\Lambda)-E_{K,s}(U)|\le\frac{2^5s}{K}\|\log\Lambda\|_1.$$
--   Only $\Lambda$ is positive definite; $U$ may be singular. This controls the error from approximate congruence filters with the paper's exact coefficient.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma A.1, p. 26.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_A_1 (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (s : ℝ) (hs : 0 < s) (U Λ : Mat d) (hU : U.IsHermitian) (hUs : opNorm U ≤ s)
    (hΛ : Λ.PosDef) (hΛI : lePSD Λ 1) :
  |traceError K s (Λ * U * Λ) - traceError K s U| ≤
    (2 : ℝ)^5*s/K * QAlgorithms.traceNorm (logMat Λ) := by sorry

end OptimalTraceDistance.Estimation
