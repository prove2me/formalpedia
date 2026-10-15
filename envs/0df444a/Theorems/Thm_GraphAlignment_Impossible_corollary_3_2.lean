-- Prove2me | Theorems.Thm_GraphAlignment_Impossible_corollary_3_2
-- name    : GraphAlignment.Impossible.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:31.808278+00:00
-- url     : https://prove2.me/theorems/b9e041f1-479d-450f-8486-f13bef3c37ee
-- title:
--   Corollary 3.2, p. 11 — for any algorithm, ℙ(β(π̂, π*) < α) ≥ 1 − (I(π*; (A, B)) + 1)/log(M/M_α)
-- statement:
--   Let $\pi^*$ be drawn uniformly from the $n!$ permutations of $\{1,\dots,n\}$, and let $G_A,G_B$ with adjacency matrices $A,B$ be generated from the correlated Erdős–Rényi model $(n,q,s)$ with planted permutation $\pi^*$, where $0\le q<s\le1$. Let $\hat\pi$ be produced by any (possibly randomized) algorithm from $(A,B)$. Let $M=n!$ and
--   $$
--   M_\alpha=\max_{\pi^*}\big|\{\pi\mid\beta(\pi,\pi^*)\ge\alpha\}\big| .
--   $$
--   If $M_\alpha<M$, then
--   $$
--   \mathbb P\big(\beta(\hat\pi,\pi^*)<\alpha\big)\;\ge\;1-\frac{I(\pi^*;(A,B))+1}{\log(M/M_\alpha)} .
--   $$
--
--   This is the instance of the generalized Fano inequality (Theorem 3.1) with hypotheses the permutations, data $(A,B)$ and distance $1-\beta$; the paper calls it the cornerstone of the impossibility proof.
--
--   **Formalization Note** The page writes $\beta(\pi,\pi^*)$ inside the probability; the estimate $\hat\pi$ is meant. The algorithm is a stochastic kernel from $(A,B)$ to permutations. The hypothesis $M_\alpha<M$ is added for the reason given for Theorem 3.1 (it holds for $n\ge2$ and $\alpha>0$, since a derangement has overlap $0$). The mutual information is that of the joint law of $(\pi^*,(A,B))$ with $\pi^*$ uniform, in nats. The standing assumptions $0\le q<s\le1$ make $\prod_eP(\omega_e)$ a probability law.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 11, Corollary 3.2

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_Setting

namespace GraphAlignment.Impossible

theorem corollary_3_2 (n : ℕ) (q s α : ℝ) (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1)
    (alg : Alg n) (hM : Mα n α < n.factorial) :
    1 - (mutualInfo (jointObs (n := n) q s) + 1) /
        Real.log ((n.factorial : ℝ) / (Mα n α : ℝ)) ≤ failProb q s α alg := by sorry

end GraphAlignment.Impossible
