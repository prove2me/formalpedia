-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_4_2
-- name    : OptimalTraceDistance.Estimation.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:45:14.06082+00:00
-- url     : https://prove2.me/theorems/764cf557-33cc-466f-9389-21c9709b015b
-- title:
--   Lemma 4.2 — cycle moment
-- statement:
--   Let $R\succeq0$, $\operatorname{tr}R\le1$, and $\|R\|_\infty\le\beta$ for $\beta>0$. For every integer $j\ge1$, the average $C_j$ of the $j$-cycle permutation operators, with $C_1=I$, satisfies
--   $$\operatorname{tr}(R^{\otimes j}C_j^2)\le\min\left\{1,\frac{\prod_{\ell=0}^{j-1}(1+\ell\beta)}{(j-1)!}\right\}.$$
--   This keeps the factorial improvement from cycle averaging and allows singular or zero $R$.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 4.2, p. 15.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_4_2 (d j : ℕ) (hd : 0 < d) (hj : 1 ≤ j)
    (R : Mat d) (hR : R.PosSemidef) (htr : tr R ≤ 1)
    (β : ℝ) (hβ : 0 < β) (hnorm : opNorm R ≤ β) :
  tr (powerState R j * (cycleAverage d j)^2) ≤ min 1 (cycleFactor β j) := by sorry

end OptimalTraceDistance.Estimation
