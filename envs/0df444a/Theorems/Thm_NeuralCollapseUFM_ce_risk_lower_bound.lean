-- Prove2me | Theorems.Thm_NeuralCollapseUFM_ce_risk_lower_bound
-- name    : NeuralCollapseUFM.ce_risk_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:17:19.641571+00:00
-- url     : https://prove2.me/theorems/afb7e312-b55b-4a38-95d0-d86dda5f3c83
-- title:
--   Lemma B.3: lower bound for the cross-entropy term at critical points
-- statement:
--   Let $K\ge2$, $n\ge1$, $N=nK$ and $\lambda_W,\lambda_H,\lambda_b>0$. Let $(W,H,b)$ be a critical point of $f$ in (14), let $\rho=\|W\|_F^2$, and let $c_1>0$, with $c_2$ as in Lemma B.5. Then
--
--   $$g(WH+b1^\top)\ge-\frac{\rho}{(1+c_1)(K-1)}\sqrt{\frac{\lambda_W}{\lambda_Hn}}+c_2.$$
--
--   Together with $\frac{\lambda_W}2\|W\|_F^2+\frac{\lambda_H}2\|H\|_F^2=\lambda_W\rho$ at critical points, this gives the lower bound $\xi(\rho)$ on $f$ used for Theorem 3.1.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix B.2, Lemma B.3, eq. (19), p. 32

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem ce_risk_lower_bound {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x) (c1 : ℝ)
    (hc1 : 0 < c1) :
    -(frobSq x.1) / ((1 + c1) * ((K : ℝ) - 1)) * Real.sqrt (lamW / (lamH * n)) + cTwo K c1 ≤
      ceRisk (logits x.1 x.2.1 x.2.2) := by sorry

end NeuralCollapseUFM
