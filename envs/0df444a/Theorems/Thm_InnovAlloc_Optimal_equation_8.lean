-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_equation_8
-- name    : InnovAlloc.Optimal.equation_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:26.203765+00:00
-- url     : https://prove2.me/theorems/d0ab6c5e-6a74-489c-a589-9567b45f585e
-- title:
--   Equation (8), p. 12 — principal profit from one innovator
-- statement:
--   Fix $\alpha\in[0,1]$, $\gamma\in(0,1)$, and a positive total investment $B$. When the principal assigns $(B,0)$ to the two agents, an effort equilibrium exists and every such equilibrium gives principal profit
--
--   $$\Pi_m(B)=\begin{cases}0,&\gamma B\le1,\\(1-\gamma)\bigl(1-1/(\gamma B)\bigr),&\gamma B>1.\end{cases}$$
--
--   This is the monopoly benchmark against which the equal-split profit is compared. The statement evaluates profit from the agents' effort equilibrium, rather than treating the closed form as the definition of an equilibrium.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 12, eq. (8)

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Equation (8), p. 12: the principal's profit at the one-agent allocation. -/
theorem equation_8 (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B) :
    (∃ x1 x2, IsEquilibrium α γ B 0 x1 x2) ∧
    ∀ x1 x2, IsEquilibrium α γ B 0 x1 x2 →
      principalProfit α γ B 0 x1 x2 = profitMono γ B := by sorry

end InnovAlloc.Optimal
