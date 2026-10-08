-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_theorem_1_3
-- name    : GivenDegreeSeq.MLE.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:45:01.211832+00:00
-- url     : https://prove2.me/theorems/5118d519-9b3e-4eb0-b2f5-9e289842f8b6
-- title:
--   Theorem 1.3 — with probability $\ge 1-C(L)n^{-2}$ the $\beta$-model MLE exists, is unique, and $|\hat\beta-\beta|_\infty\le C(L)\sqrt{\log n/n}$
-- statement:
--   Let $L\ge 0$. There is a constant $C=C(L)>0$, depending only on $L$, such that the following holds for every $n\ge 1$ and every $\beta\in\mathbb R^n$ with $|\beta_i|\le L$ for all $i$. Let $G$ be drawn from the $\beta$-model $\mathbb P_\beta$ and let $d_1,\dots,d_n$ be its degree sequence. Then with probability at least $1-C n^{-2}$ the maximum likelihood equations
--   $$d_i=\sum_{j\ne i}\frac{e^{\hat\beta_i+\hat\beta_j}}{1+e^{\hat\beta_i+\hat\beta_j}},\qquad i=1,\dots,n,$$
--   have a solution $\hat\beta$, this solution is unique, and
--   $$\max_{1\le i\le n}|\hat\beta_i-\beta_i|\le C\sqrt{\frac{\log n}{n}}.$$
--
--   Although the number of parameters grows with the number of vertices, the MLE estimates all of them uniformly, at the rate $\sqrt{\log n/n}$, from a single observed graph.
--
--   **Formalization Note** The constant $C$ is chosen before $n$ and $\beta$ (choosing it after would make the statement trivial, since $1-Cn^{-2}<0$ for large $C$). The paper's $L:=\max_i|\beta_i|$ becomes the hypothesis $|\beta_i|\le L$; the two readings agree because $C(L)$ may be taken nondecreasing. The probability is $\mathbb P_\beta$ of the event, compared in $[0,\infty]$ with $\max(0,1-Cn^{-2})$. The norm is the sup norm.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 7, Theorem 1.3 (proof pp. 16–21)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_BetaModel

namespace GivenDegreeSeq.MLE

/-- Theorem 1.3, p. 7. For every `L ≥ 0` there is a constant `C = C(L) > 0`, depending only on
`L`, such that for every `n ≥ 1` and every `β ∈ ℝⁿ` with `|β_i| ≤ L` for all `i`: if `G` is drawn
from `P_β` with degree sequence `d`, then with probability at least `1 − C n⁻²` the ML equations
(3) have a solution `β̂`, this solution is unique, and `max_i |β̂_i − β_i| ≤ C √(log n / n)`. -/
theorem theorem_1_3 :
    ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ β : Fin n → ℝ, (∀ i, |β i| ≤ L) →
      ENNReal.ofReal (1 - C / (n : ℝ) ^ 2) ≤
        betaModel β {G | ∃ βhat : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq (deg G) βhat ∧
          (∀ b : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq (deg G) b → b = βhat) ∧
          ‖βhat - β‖ ≤ C * Real.sqrt (Real.log n / n)} := by sorry

end GivenDegreeSeq.MLE
