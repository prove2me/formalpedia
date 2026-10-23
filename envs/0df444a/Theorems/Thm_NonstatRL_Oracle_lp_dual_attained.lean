-- Prove2me | Theorems.Thm_NonstatRL_Oracle_lp_dual_attained
-- name    : NonstatRL.Oracle.lp_dual_attained
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T18:11:27.240693+00:00
-- url     : https://prove2.me/theorems/7ed72e06-f640-416f-ab52-888b45e80b1f
-- title:
--   LP duality for (15)–(16), p. 33 — the dual attains the optimal gain
-- statement:
--   For a finite MDP with reward $r$, transition kernel $p$ and allowed action sets $\mathcal A_s$, let $\rho^*$ be the optimal value of the occupancy-measure LP $P(r,p)$ in (15):
--   $$\max\sum_{s,\,a\in\mathcal A_s}r(s,a)x(s,a)\quad\text{s.t.}\quad\sum_{a\in\mathcal A_s}x(s,a)=\sum_{s',\,a'\in\mathcal A_{s'}}p(s|s',a')x(s',a'),\ \sum x=1,\ x\ge0.$$
--   Then the dual LP $D(r,p)$ in (16) has an optimal solution at this value: there is $\gamma:\mathcal S\to\mathbb R$ with
--   $$\rho^*+\gamma(s)\ge r(s,a)+\sum_{s'}p(s'|s,a)\gamma(s')\qquad\text{for all } s,\ a\in\mathcal A_s.$$
--   This is the LP strong-duality fact behind the first sentence of Appendix A.2. Here $\rho^*$ is the supremum of the primal values, and it is attained by the dual.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, Appendix A.1, p. 33, LPs (15)–(16) and the opening sentence of Appendix A.2 (existence of an optimal solution $(\rho^*_t,\gamma^*_t)$ of $D(r_t,p_t)$); LP duality as in Puterman 1994, Section 8.8

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

/-- LP duality for (15)–(16), Appendix A.1, p. 33: the dual D(r,p) has a feasible
solution whose ρ-component equals the optimal value of P(r,p). -/
theorem lp_dual_attained {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) :
    ∃ γ : Fin S → ℝ,
      DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As (optGain M As) γ := by sorry

end NonstatRL.Oracle
