-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_equations_10_11
-- name    : InnovAlloc.Optimal.equations_10_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:27.092826+00:00
-- url     : https://prove2.me/theorems/2091b930-0355-4d97-996b-fc28674fb1ff
-- title:
--   Equations (10)–(11), p. 13 — equal-split failure rates and principal profit
-- statement:
--   Fix $\alpha\in[0,1]$, $\gamma\in(0,1)$, and an investment $B$ satisfying $\gamma B>2$. Under the equal allocation $(B/2,B/2)$, an effort equilibrium exists in which both agents have the failure probability
--
--   $$y^*=\frac{4}{\alpha B\gamma+\sqrt{B\gamma}\sqrt{8-8\alpha+\alpha^2B\gamma}},$$
--
--   and the principal earns
--
--   $$\Pi_d(B)=(1-\gamma)\left(\alpha-\frac4{\gamma B}+\sqrt{\frac{\gamma\alpha^2B-8\alpha+8}{\gamma B}}\right).$$
--
--   For $\alpha>0$, every equilibrium of this equal-allocation game has these failure probabilities and this profit. These formulas supply the two-agent benchmark for Theorem 1.
--
--   **Formalization Note** At $\alpha=0$, an equal split can have a continuum of equilibria, so the uniqueness clause requires $\alpha>0$; the existence clause retains $\alpha=0$.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 13, eqs. (10)–(11)

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Equations (10)–(11), p. 13: equal-allocation failure rates and profit. -/
theorem equations_10_11 (α γ B : ℝ) (hs : Standing α γ) (hB : 2 < γ * B) :
    (∃ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 ∧
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) ∧
    (0 < α → ∀ x1 x2, IsEquilibrium α γ (B / 2) (B / 2) x1 x2 →
      Real.exp (-(B / 2 * x1)) = yStar α γ B ∧
      Real.exp (-(B / 2 * x2)) = yStar α γ B ∧
      principalProfit α γ (B / 2) (B / 2) x1 x2 = profitDuo α γ B) := by sorry

end InnovAlloc.Optimal
