-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_theorem_1
-- name    : InnovAlloc.Optimal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:43.666051+00:00
-- url     : https://prove2.me/theorems/ea70d65c-10c0-42d4-bd38-b3baef5cbc1d
-- title:
--   Theorem 1, p. 15 — optimal allocation between one and two innovators
-- statement:
--   Let the principal have capacity $\bar B>0$. The two innovators choose nonnegative efforts in a simultaneous game, receive the fraction $\gamma\in(0,1)$ of their own product profits, and compete with two-product profit parameter $\alpha\in[0,1]$. Success probability is $1-e^{-b_ix_i}$, and innovations are independent. An allocation is optimal if it is feasible, has an effort equilibrium, and every equilibrium at it earns the principal at least as much as every equilibrium of every feasible allocation.
--
--   Write $a_0=6\sqrt2-8$ and, when $a_0<\alpha<1/2$, write $L(\alpha)$ and $H(\alpha)$ for $\frac{1-\alpha\mp\sqrt{\alpha^2+16\alpha-8}}{1-2\alpha}$. The optimal allocations named by the theorem are:
--
--   1. If $\gamma\bar B\le1$, invest nothing: $(0,0)$, earning zero.
--   2. If $1<\gamma\bar B\le2$, invest all in one innovator: $(\bar B,0)$.
--   3. If $\gamma\bar B>2$ and $\alpha\le a_0$, choose $(\bar B,0)$.
--   4. If $\gamma\bar B>2$ and $a_0<\alpha<1/2$, choose $(\bar B/2,\bar B/2)$ exactly when $\gamma\bar B\in[L(\alpha),H(\alpha)]$, and $(\bar B,0)$ otherwise.
--   5. If $\gamma\bar B>2$ and $\alpha\ge1/2$, choose $(\bar B/2,\bar B/2)$ once $\gamma\bar B$ reaches the lower threshold, and $(\bar B,0)$ below it.
--
--   This gives the principal's full strategy across the capacity and competition regimes. Ties at the stated boundaries are allowed; the names do not assert uniqueness up to agent relabelling.
--
--   **Formalization Note** At $\alpha=1/2$, the printed region-c threshold is $0/0$; this formalization corrects it to $9$, its continuous limit and the true comparison threshold. The theorem quantifies over all effort equilibria rather than assigning a closed form as the equilibrium by definition.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 15, Theorem 1; p. 39, proof

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Theorem 1, p. 15: the principal's optimal allocation by resource abundance and
    product competition. The region-c threshold is corrected at `α = 1/2`. -/
theorem theorem_1 (α γ Bbar : ℝ) (hs : Standing α γ) (hB : 0 < Bbar) :
    (γ * Bbar ≤ 1 → IsOptimal α γ Bbar 0 0 ∧
      ∀ x1 x2, IsEquilibrium α γ 0 0 x1 x2 →
        principalProfit α γ 0 0 x1 x2 = 0) ∧
    (1 < γ * Bbar → γ * Bbar ≤ 2 →
      IsOptimal α γ Bbar Bbar 0) ∧
    (2 < γ * Bbar →
      (α ≤ alphaLow → IsOptimal α γ Bbar Bbar 0) ∧
      (alphaLow < α → α < 1 / 2 →
        (γ * Bbar ∈ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar ∉ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar Bbar 0)) ∧
      (1 / 2 ≤ α →
        (cThreshold α ≤ γ * Bbar →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar < cThreshold α →
          IsOptimal α γ Bbar Bbar 0))) := by sorry

end InnovAlloc.Optimal
