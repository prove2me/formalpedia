-- Prove2me | Theorems.Thm_GreedyRS_Greedy_lemma2_zero_part
-- name    : GreedyRS.Greedy.lemma2_zero_part
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T11:18:09.918052+00:00
-- url     : https://prove2.me/theorems/a1f8ca2c-559c-47b1-9b39-b73b75b28392
-- title:
--   Lemma 2 (x = 0), p. 14 — Pr{Ñ(0) < ∞} = 1 and E[Ñ(0)] = ∞
-- statement:
--   Let $Z_1,Z_2,\dots$ be i.i.d. $N(0,1)$, $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$, and $\tilde N(0)=\inf\{n\ge1:\bar Z(n)<0\}$, with $\tilde N(0)=\infty$ if this never happens. Then
--   $$\Pr\{\tilde N(0)<\infty\}=1\qquad\text{and}\qquad\mathrm E\big[\tilde N(0)\big]=\infty.$$
--
--   This is the $x=0$ part of Lemma 2. The driftless Gaussian random walk $\sum_{j\le n}Z_j$ becomes negative almost surely, but the expected time until it first does so is infinite.
--
--   **Formalization Note.** $\tilde N(0)$ is `crossTime 0 1` on `stdNormalSeq`, the law of an i.i.d. $N(0,1)$ sequence on $\mathbb R^{\mathbb N}$. $\mathrm E[\tilde N(0)]$ is `Cn0 0 1`, a lower Lebesgue integral in $[0,\infty]$, so "$=\infty$" is literal.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 14, Lemma 2 (case x = 0); the paper attributes it to Siegmund (1985), Sequential Analysis, Corollaries 8.39 and 8.44

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy

theorem lemma2_zero_part :
    stdNormalSeq {z | crossTime 0 1 z < ⊤} = 1 ∧ Cn0 0 1 = ⊤ := by sorry

end GreedyRS.Greedy
