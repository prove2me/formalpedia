-- Prove2me | Theorems.Thm_HeldWolfeCrowder_Assignment_max_w_eq_assignment_cost
-- name    : HeldWolfeCrowder.Assignment.max_w_eq_assignment_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:53:10.150826+00:00
-- url     : https://prove2.me/theorems/fde0a531-84a2-494b-9b0e-432755feb3c4
-- title:
--   §3, Eqs. (3.1)–(3.3) — max w equals the cost of an optimal assignment
-- statement:
--   Let $A=(a_{ir})$ be a real $n\times n$ cost matrix, let $w(\pi)=\sum_i\pi_i+\sum_r\min_s[a_{sr}-\pi_s]$ be the dual function (3.3), and let $\sigma$ be an optimal one-to-one assignment: a permutation with $\sum_r a_{\sigma(r)\,r}\le\sum_r a_{\tau(r)\,r}$ for every permutation $\tau$. Then $w$ attains its maximum over $\mathbb R^n$, and
--
--   $$\max_{\pi\in\mathbb R^n} w(\pi)=\sum_{r=1}^n a_{\sigma(r)\,r}.$$
--
--   This is the duality the paper invokes at the start of Section 3: the linear relaxation of the assignment problem (3.1) has an integral optimal solution, so its value is the optimal assignment cost; by linear-programming duality it equals the value of (3.2), and eliminating $\rho$ from (3.2) gives $w$. It is what makes the maximizers of $w$ the optimal dual prices of the assignment problem.
--
--   **Formalization Note** "$w$ attains its maximum, equal to $c$" is `IsGreatest (Set.range (w a)) c`.
-- source:
--   Held, Wolfe & Crowder, Validation of subgradient optimization, Math. Programming 6 (1974), p. 69, §3, Eqs. (3.1)–(3.3)

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting

namespace HeldWolfeCrowder.Assignment

/-- Held–Wolfe–Crowder (1974), §3, p. 69, Eqs. (3.1)–(3.3): the optimal value of the assignment
problem is that of the dual (3.2), whose objective maximized over `ρ` is `w` of (3.3). So `w`
attains its maximum, and its maximum value is the cost of an optimal one-to-one assignment. -/
theorem max_w_eq_assignment_cost {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsOptimalAssignment a σ) :
    IsGreatest (Set.range (w a)) (assignCost a σ) := by sorry

end HeldWolfeCrowder.Assignment
