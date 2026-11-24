-- Prove2me | Theorems.Thm_NeuralCollapseUFM_no_spurious_local_minima_strict_saddle
-- name    : NeuralCollapseUFM.no_spurious_local_minima_strict_saddle
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:20:02.073842+00:00
-- url     : https://prove2.me/theorems/73a80ddb-dd93-4458-a055-391fa3351e10
-- title:
--   Theorem 3.2 (as proved): no spurious local minima and the strict saddle property
-- statement:
--   Let $K\ge2$ classes with $n\ge1$ samples each, feature dimension $d>K$, and $\lambda_W,\lambda_H,\lambda_b>0$. For the objective
--
--   $$f(W,H,b)=\frac1{Kn}\sum_{k=1}^K\sum_{i=1}^n\mathcal L_{CE}(Wh_{k,i}+b,y_k)+\frac{\lambda_W}2\|W\|_F^2+\frac{\lambda_H}2\|H\|_F^2+\frac{\lambda_b}2\|b\|_2^2$$
--
--   of (4):
--
--   1. every local minimizer of $f$ is a global minimizer and has the form of Theorem 3.1;
--   2. every critical point of $f$ that is not a local minimizer is a strict saddle: the Hessian $\nabla^2f(W,H,b)$ has at least one negative eigenvalue, that is, $\nabla^2f(W,H,b)[\Delta,\Delta]<0$ for some direction $\Delta$.
--
--   So the regularized cross-entropy loss of the unconstrained feature model has a benign landscape: no spurious local minima, and the saddle points can be escaped along negative curvature.
--
--   **Formalization Note** The main-text statement also says that the Hessian at a strict saddle is "non-degenerate". This is false: at a critical point with $W\ne0$, the curve $t\mapsto(We^{tA},e^{-tA}H,b)$ with $A$ skew-symmetric consists of critical points, so its tangent lies in the kernel of the Hessian. The restatement in Appendix C (Theorem C.1) and its proof omit this clause, and so does the Lean statement. The form of Theorem 3.1 is the one in its as-proved statement.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Section 3.2, Theorem 3.2, p. 10; restated as Theorem C.1, p. 37, proof pp. 38-40

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem no_spurious_local_minima_strict_saddle {K d n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (hd : K < d) (lamW lamH lamb : ℝ) (hW : 0 < lamW) (hH : 0 < lamH) (hb : 0 < lamb) :
    (∀ x : Params K d n, IsLocalMin (objective lamW lamH lamb) x →
      IsGlobalMinimizer (objective lamW lamH lamb) x ∧ IsCollapsedSolution lamW lamH lamb x) ∧
    (∀ x : Params K d n, IsCriticalPoint (objective lamW lamH lamb) x →
      ¬ IsLocalMin (objective lamW lamH lamb) x → IsStrictSaddle (objective lamW lamH lamb) x) := by sorry

end NeuralCollapseUFM
