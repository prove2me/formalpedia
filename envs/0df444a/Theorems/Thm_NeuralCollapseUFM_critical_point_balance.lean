-- Prove2me | Theorems.Thm_NeuralCollapseUFM_critical_point_balance
-- name    : NeuralCollapseUFM.critical_point_balance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:16:11.280848+00:00
-- url     : https://prove2.me/theorems/7957b25f-8ce9-48aa-a2d9-3fff497da187
-- title:
--   Lemma B.2: balance of $W$ and $H$ at critical points
-- statement:
--   Let $K\ge2$, $n\ge1$ and $\lambda_W,\lambda_H,\lambda_b>0$, and let $(W,H,b)$ be a critical point of the objective $f$ of (14). Then
--
--   $$W^\top W=\frac{\lambda_H}{\lambda_W}HH^\top\qquad\text{and}\qquad\rho:=\|W\|_F^2=\frac{\lambda_H}{\lambda_W}\|H\|_F^2.$$
--
--   This balance between the classifier and the features is used in the proofs of Theorems 3.1 and 3.2.
--
--   **Formalization Note** "Critical point" means that every directional derivative of $f$ at $(W,H,b)$ vanishes, which is the same as $\nabla f(W,H,b)=0$ because $f$ is smooth.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix B.2, Lemma B.2, eq. (16), p. 31

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem critical_point_balance {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) :
    x.1ᵀ * x.1 = (lamH / lamW) • (x.2.1 * x.2.1ᵀ) ∧
      frobSq x.1 = lamH / lamW * frobSq x.2.1 := by sorry

end NeuralCollapseUFM
