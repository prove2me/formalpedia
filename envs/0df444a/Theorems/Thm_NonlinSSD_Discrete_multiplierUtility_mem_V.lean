-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_multiplierUtility_mem_V
-- name    : NonlinSSD.Discrete.multiplierUtility_mem_V
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:22.085921+00:00
-- url     : https://prove2.me/theorems/8e7da0bb-8ab3-416d-9d53-39c1bca371d9
-- title:
--   p. 18, proof of Theorem 6 — the utility (46) of nonnegative multipliers belongs to V_i
-- statement:
--   Let $y_{i1},\dots,y_{in}$ be real numbers and $\mu_{i1},\dots,\mu_{in} \ge 0$. Then the function
--   $$u_i(t) = -\sum_{k=1}^n \mu_{ik} (y_{ik} - t)_+$$
--   belongs to $V_i$: it is concave and nondecreasing on $\mathbb R$, piecewise linear with break points only at the $y_{ik}$, and $u_i(t) = 0$ for every $t \ge \max_k y_{ik}$.
--
--   This is the paper's sentence "We have shown that the Lagrange multipliers generate a utility function", the first half of the correspondence between nonnegative multipliers and utilities in $V_i$ used in Theorem 6.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 18, proof of Theorem 6, with Eq. (46) (p. 17) and the definition of V_i (p. 16)

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem multiplierUtility_mem_V {n : ℕ} (y μ : Fin n → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    InV y (multiplierUtility y μ) := by sorry

end NonlinSSD.Discrete
