-- Prove2me | Theorems.Thm_NeuralCollapseUFM_convex_program_lower_bound
-- name    : NeuralCollapseUFM.convex_program_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:18:58.163698+00:00
-- url     : https://prove2.me/theorems/5c3854ab-5039-4848-8051-091166302cc0
-- title:
--   Lemma C.2: the convex program (37) bounds the objective from below
-- statement:
--   Let $K\ge2$, $n\ge1$, $N=nK$, $\lambda_W,\lambda_H,\lambda_b>0$, and let $(Z^\star,b^\star)$ be a global minimizer of the convex program
--
--   $$\tilde f(Z,b)=g(Z+b1^\top)+\sqrt{\lambda_W\lambda_H}\,\|Z\|_*+\frac{\lambda_b}2\|b\|_2^2,\qquad Z\in\mathbb{R}^{K\times N},\ b\in\mathbb{R}^K.$$
--
--   Then $\tilde f(Z^\star,b^\star)\le f(W,H,b)$ for all $W\in\mathbb{R}^{K\times d}$, $H\in\mathbb{R}^{d\times N}$, $b\in\mathbb{R}^K$.
--
--   The convex program is the lower model through which Theorem 3.2 certifies global optimality.
--
--   **Formalization Note** The lemma does not restrict $d$, and neither does the Lean statement.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix C.2, Lemma C.2, eqs. (37)-(38), pp. 38 and 40

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem convex_program_lower_bound {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (Z : Matrix (Fin K) (Fin K × Fin n) ℝ) (b : Fin K → ℝ)
    (hmin : ∀ (Z' : Matrix (Fin K) (Fin K × Fin n) ℝ) (b' : Fin K → ℝ),
      convexObjective lamW lamH lamb Z b ≤ convexObjective lamW lamH lamb Z' b') :
    ∀ x : Params K d n, convexObjective lamW lamH lamb Z b ≤ objective lamW lamH lamb x := by sorry

end NeuralCollapseUFM
