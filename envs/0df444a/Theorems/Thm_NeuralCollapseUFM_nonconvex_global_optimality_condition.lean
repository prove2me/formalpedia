-- Prove2me | Theorems.Thm_NeuralCollapseUFM_nonconvex_global_optimality_condition
-- name    : NeuralCollapseUFM.nonconvex_global_optimality_condition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:19:33.74334+00:00
-- url     : https://prove2.me/theorems/9fca252d-0c68-437b-a1b4-61b2aa1c42c1
-- title:
--   Lemma C.4: a critical point with $\|\nabla g\|\le\sqrt{\lambda_W\lambda_H}$ is a global minimizer
-- statement:
--   Let $K\ge2$, $n\ge1$ and $\lambda_W,\lambda_H,\lambda_b>0$. If $(W,H,b)$ is a critical point of $f$ in (14) and
--
--   $$\big\|\nabla g(WH+b1^\top)\big\|\le\sqrt{\lambda_W\lambda_H},$$
--
--   where $\|\cdot\|$ is the spectral norm, then $(W,H,b)$ is a global minimizer of $f$.
--
--   This criterion sorts the critical points into global minimizers and the remaining set $\mathcal C_2$, where the proof of Theorem 3.2 constructs a direction of negative curvature.
--
--   **Formalization Note** $\nabla g$ is written out as $[\nabla g(Z)]_{j,(k,i)}=\frac1N(\operatorname{softmax}(z_{k,i})_j-\mathbb 1[j=k])$. The lemma does not restrict $d$, and neither does the Lean statement.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix C.2, Lemma C.4, eq. (43), p. 41

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem nonconvex_global_optimality_condition {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb)
    (x : Params K d n) (hx : IsCriticalPoint (objective lamW lamH lamb) x)
    (hg : opNorm (ceRiskGrad (logits x.1 x.2.1 x.2.2)) ≤ Real.sqrt (lamW * lamH)) :
    IsGlobalMinimizer (objective lamW lamH lamb) x := by sorry

end NeuralCollapseUFM
