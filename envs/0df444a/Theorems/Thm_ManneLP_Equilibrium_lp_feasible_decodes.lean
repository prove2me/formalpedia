-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_lp_feasible_decodes
-- name    : ManneLP.Equilibrium.lp_feasible_decodes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:39.85448+00:00
-- url     : https://prove2.me/theorems/58416724-ddce-4237-be50-e1a3ca7a76d6
-- title:
--   §3, N.B. — every feasible xᵢⱼ is yᵢq(j | i) for the decoded rule q(j | i) = xᵢⱼ / Σⱼxᵢⱼ in statistical equilibrium y
-- statement:
--   Consider Manne's inventory model and let $x$ be a feasible point of the linear program: $x_{ij}\ge0$ on the admissible pairs, $\sum_{i,j}x_{ij}=1$, and (8.1)–(8.T). Put
--   $$
--   y_i=\sum_j x_{ij},\qquad q(j\mid i)=\frac{x_{ij}}{y_i}\ \ (y_i\ne 0),
--   $$
--   with $q(0\mid i)=1$ (produce nothing) at stock levels where $y_i=0$. Then
--
--   1. $q$ is a stationary randomized decision rule;
--   2. $y$ is a statistical equilibrium of $q$: a probability vector with $y_t=\sum_iy_iP_q(i,t)$ for $t=0,\dots,T$;
--   3. $x_{ij}=y_i\,q(j\mid i)$ for every admissible pair $(i,j)$.
--
--   Together with the converse (every rule in equilibrium gives a feasible point), this makes the feasible set of the linear program exactly the set of equilibrium joint laws of (initial stock, production quantity) over all stationary randomized rules.
--
--   **Formalization Note** The page's quotient is $0/0$ at stock levels that are never visited; the default action $j=0$ there is a choice of the formalization (any admissible default would do). Equation (8.0) is not among the hypotheses.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 261 (PDF p. 4), §3, N.B.; with (3), (8.0)–(8.T) on p. 262

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem lp_feasible_decodes (M : Model) (x : ℕ × ℕ → ℝ) (hx : IsLPFeasible M x) :
    IsRule M (decodeRule M x) ∧ IsEquilibrium M (decodeRule M x) (decodeDist M x) ∧
      ∀ a ∈ M.A, x a = jointLaw (decodeDist M x) (decodeRule M x) a := by sorry

end ManneLP.Equilibrium
