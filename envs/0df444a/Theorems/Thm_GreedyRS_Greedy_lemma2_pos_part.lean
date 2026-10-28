-- Prove2me | Theorems.Thm_GreedyRS_Greedy_lemma2_pos_part
-- name    : GreedyRS.Greedy.lemma2_pos_part
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T11:18:13.732572+00:00
-- url     : https://prove2.me/theorems/a8c29aaa-a825-4ec1-bf9d-adcf8c6acdf0
-- title:
--   Lemma 2 (x > 0), p. 14 — Pr{Ñ(x) < ∞} = 1 and E[Ñ(x)] = exp(Σ Φ(−√n x)/n) = C(x)
-- statement:
--   Let $Z_1,Z_2,\dots$ be i.i.d. $N(0,1)$ and $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$. For $x\in\mathbb R$ let $\tilde N(x)=\inf\{n\ge1:\bar Z(n)<x\}$ be the first time the running average drops below $x$, with $\tilde N(x)=\infty$ if this never happens. Let $\Phi$ be the standard normal distribution function. Then for every $x>0$,
--   $$\Pr\{\tilde N(x)<\infty\}=1\qquad\text{and}\qquad\mathrm E\big[\tilde N(x)\big]=\exp\Big(\sum_{n=1}^\infty\frac1n\,\Phi\big(-\sqrt n\,x\big)\Big)=C(x).\qquad(4.1)$$
--
--   This is the $x>0$ part of Lemma 2. It is Spitzer's identity for the expected first descending ladder epoch of the Gaussian random walk $\sum_{j\le n}(Z_j-x)$, which has negative drift. It identifies $C(x)$ as the mean boundary-crossing time used throughout the paper.
--
--   **Formalization Note.** $\tilde N(x)$ is `crossTime x 1` on `stdNormalSeq`, the law of an i.i.d. $N(0,1)$ sequence on $\mathbb R^{\mathbb N}$. $\mathrm E[\tilde N(x)]$ is `Cn0 x 1`, a lower Lebesgue integral in $[0,\infty]$. $C$ is `Cfun`.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 14, Lemma 2 (case x > 0, eq. (4.1)); the paper attributes it to Siegmund (1985), Sequential Analysis, Corollaries 8.39 and 8.44

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy

theorem lemma2_pos_part (x : ℝ) (hx : 0 < x) :
    stdNormalSeq {z | crossTime x 1 z < ⊤} = 1 ∧ Cn0 x 1 = ENNReal.ofReal (Cfun x) := by sorry

end GreedyRS.Greedy
