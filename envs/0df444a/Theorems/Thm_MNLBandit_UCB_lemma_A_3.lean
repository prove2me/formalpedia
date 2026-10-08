-- Prove2me | Theorems.Thm_MNLBandit_UCB_lemma_A_3
-- name    : MNLBandit.UCB.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:34:04.365455+00:00
-- url     : https://prove2.me/theorems/e34aba8b-aee2-4602-86ee-09a9804b94a3
-- title:
--   Lemma A.3, p. 35 — the revenue of an optimal assortment does not decrease when the MNL parameters increase
-- statement:
--   Let $\mathcal S$ be a family of assortments closed under taking subsets, let $r_i\in[0,1]$ be revenues, and let $w,u$ be parameter vectors with $0\le w_i\le u_i$ for all $i$. Suppose $S\in\mathcal S$ is an optimal assortment for the parameters $w$, i.e. $R(S,w)\ge R(Q,w)$ for every $Q\in\mathcal S$, and that $w_j>0$ for every $j\in S$. Then
--   $$
--   R(S,u)\ge R(S,w),\qquad R(S,w)=\frac{\sum_{i\in S}r_iw_i}{1+\sum_{j\in S}w_j}.
--   $$
--   The expected revenue is not monotone in the parameters in general; only the revenue of an optimal assortment is. This is what makes the optimistic assortment of Algorithm 1 overestimate the optimal revenue (Lemma 4.2).
--
--   **Formalization Note.**
--   1. The page assumes $0\le w_i$. The hypothesis $w_j>0$ for $j\in S$ is added because the printed statement is false without it. Example: $S=\{1,2\}$, $r=(1,0)$, $w=(1,0)$, $\mathcal S$ all subsets of $\{1,2\}$. Then $S$ is optimal ($R=1/2$, tied with $\{1\}$), and $u=(1,1)$ gives $R(S,u)=1/3<1/2$. The proof's step "$r_j<R(S)$ means removing $j$ increases the revenue" needs $w_j>0$.
--   2. Closure under subsets is Assumption 4.1.2, the standing assumption of §4; the proof removes products from $S$.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 35, Lemma A.3

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting

namespace MNLBandit.UCB

open ChoiceCDLP.MNL

theorem lemma_A_3 {N : ℕ} (𝒮 : Finset (Finset (Fin N))) (h𝒮 : DownClosed 𝒮)
    (r : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (w u : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwu : ∀ i, w i ≤ u i) (S : Finset (Fin N)) (hS : S ∈ 𝒮)
    (hopt : ∀ Q ∈ 𝒮, mnlObjective w r 1 Q ≤ mnlObjective w r 1 S)
    (hpos : ∀ j ∈ S, 0 < w j) :
    mnlObjective w r 1 S ≤ mnlObjective u r 1 S := by sorry

end MNLBandit.UCB
