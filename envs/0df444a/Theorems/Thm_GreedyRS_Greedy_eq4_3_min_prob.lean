-- Prove2me | Theorems.Thm_GreedyRS_Greedy_eq4_3_min_prob
-- name    : GreedyRS.Greedy.eq4_3_min_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:01.129709+00:00
-- url     : https://prove2.me/theorems/d9d6bfe9-c608-4542-965f-0bced58dcc32
-- title:
--   (4.3), p. 14 — for x < 0, Pr{min_{n≥1} Z̄(n) > x} = exp(−Σ Φ(√n x)/n) = [C(−x)]⁻¹
-- statement:
--   Let $Z_1,Z_2,\dots$ be i.i.d. $N(0,1)$ with running average $\bar Z(n)=\frac1n\sum_{j=1}^nZ_j$, let $\Phi$ be the standard normal distribution function, and let
--   $$C(x)=\exp\Bigl(\sum_{n=1}^\infty\frac1n\Phi(-\sqrt n\,x)\Bigr),\qquad x>0.$$
--   For every $x<0$,
--   $$\Pr\Bigl\{\min_{n\ge1}\bar Z(n)>x\Bigr\}=\exp\Bigl(-\sum_{n=1}^\infty\frac1n\Phi(\sqrt n\,x)\Bigr)=\bigl[C(-x)\bigr]^{-1}.$$
--
--   This is the probability that the running average never drops to the level $x$. It turns the lower bound $\Pr\{\min_n\bar X_1(n)>\mu_1-\gamma_0\}$ of Theorem 1 into the closed form $[C(\gamma_0/\sigma_1)]^{-1}$.
--
--   **Formalization Note** "$\min_{n\ge1}\bar Z(n)>x$" is encoded as: $\bar Z$ is bounded below on $n\ge1$ and $\inf_{n\ge1}\bar Z(n)>x$. By Lemma 1 the infimum is attained almost surely, so this is the paper's event up to a null set. $C$ is applied at $-x>0$, where its series converges.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 14, (4.3) and the definition of C(x) that follows it

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem eq4_3_min_prob (x : ℝ) (hx : x < 0) :
    stdNormalSeq {z | AboveFrom (zbar z) 1 x} =
      ENNReal.ofReal (Real.exp (-∑' n : ℕ,
        Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1))) ∧
    stdNormalSeq {z | AboveFrom (zbar z) 1 x} = ENNReal.ofReal (1 / Cfun (-x)) := by sorry
end GreedyRS.Greedy
