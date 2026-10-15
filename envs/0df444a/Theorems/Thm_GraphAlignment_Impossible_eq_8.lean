-- Prove2me | Theorems.Thm_GraphAlignment_Impossible_eq_8
-- name    : GraphAlignment.Impossible.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:31.420736+00:00
-- url     : https://prove2.me/theorems/d811863f-35bf-4ba2-9f25-b0dfb0590a10
-- title:
--   (8), p. 12 — I(π*; (A, B)) ≤ E_π*[D(ℙ((A, B) = · | π*) ‖ 𝒬)]
-- statement:
--   In the correlated Erdős–Rényi model $(n,q,s)$ with $0\le q<s\le1$ and $\pi^*$ uniform on the $n!$ permutations, let $\mathcal Q$ be the joint law of the adjacency matrices $(A,B)$ of two independent Erdős–Rényi graphs $G(n,q)$. Then
--   $$
--   I(\pi^*;(A,B))\;\le\;\mathbb E_{\pi^*}\Big[D\big(\mathbb P((A,B)=\cdot\mid\pi^*)\,\big\|\,\mathcal Q\big)\Big]
--   =\frac1{n!}\sum_{\tilde\pi}D\big(\mathbb P((A,B)=\cdot\mid\pi^*=\tilde\pi)\,\big\|\,\mathcal Q\big).
--   $$
--
--   The mutual information is bounded by the average divergence of the conditional laws from one fixed reference law; choosing $\mathcal Q$ to be a product law makes the right side computable pair by pair.
--
--   **Formalization Note** Natural logarithm. $\mathcal Q$ is the push-forward of the product law $\prod_e Q(\omega_e)$ of (4) through $\omega\mapsto(A,B')$. Lean's $\log(p/0)=0$ does not interfere: for $q>0$, $\mathcal Q$ is positive on every symmetric loopless pair of matrices, which carries all conditional mass; for $q=0$ all laws are the point mass at the empty graphs and both sides vanish. No hypothesis $q>0$ is added.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 12, §3.2, (8)

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_Setting

namespace GraphAlignment.Impossible

theorem eq_8 (n : ℕ) (q s : ℝ) (hq : 0 ≤ q) (hqs : q < s) (hs : s ≤ 1) :
    mutualInfo (jointObs (n := n) q s) ≤
      (1 / (n.factorial : ℝ)) * ∑ πs : Equiv.Perm (Fin n), kl (condObs q s πs) (qObs q) := by sorry

end GraphAlignment.Impossible
