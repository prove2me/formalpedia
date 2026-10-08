-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_equilibrium_satisfies_8
-- name    : ManneLP.Equilibrium.equilibrium_satisfies_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:09:26.159221+00:00
-- url     : https://prove2.me/theorems/eb43eea1-def5-4026-a658-3f98c220feaf
-- title:
--   §4, (8.0)–(8.T) — a rule in statistical equilibrium yields xᵢⱼ = yᵢq(j | i) satisfying x ≧ 0, (4) and every equation (8.0)–(8.T)
-- statement:
--   Consider Manne's inventory model. Let $q$ be a stationary randomized decision rule and $y$ a statistical equilibrium of $q$, i.e. a probability vector on $\{0,\dots,T\}$ with $y_t=\sum_i y_iP_q(i,t)$ for all $t\le T$. Then the joint probabilities $x_{ij}=y_i\,q(j\mid i)$ satisfy $x_{ij}\ge 0$ on the admissible pairs, (4) $\sum_{i,j}x_{ij}=1$, and each of the equations
--   $$
--   \text{(8.0)}\quad \sum_j x_{0j}=\sum_{\substack{i,j,n:\\ i+j-n\le 0}}p_nx_{ij},\qquad
--   \text{(8.t)}\quad \sum_j x_{tj}=\sum_{\substack{i,j,n:\\ i+j-n=t}}p_nx_{ij}\quad(t=1,\dots,T).
--   $$
--
--   This is the sense in which "equations (8.0)–(8.T) may each be interpreted as a requirement of statistical equilibrium": every equilibrium of every rule gives a feasible point of the linear program.
--
--   **Formalization Note** The equilibrium is defined as a stationary distribution of the chain of $q$, not as the equations (8), so the statement is not a restatement of a definition. No irreducibility is assumed.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 262 (PDF p. 5), §4, (8.0)–(8.T) and the paragraph following them

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem equilibrium_satisfies_8 (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ)
    (hq : IsRule M q) (hy : IsEquilibrium M q y) :
    (∀ a ∈ M.A, 0 ≤ jointLaw y q a) ∧ ∑ a ∈ M.A, jointLaw y q a = 1 ∧
      Eq80 M (jointLaw y q) ∧ ∀ t : ℕ, 1 ≤ t → t ≤ M.T → Eq8t M (jointLaw y q) t := by sorry

end ManneLP.Equilibrium
