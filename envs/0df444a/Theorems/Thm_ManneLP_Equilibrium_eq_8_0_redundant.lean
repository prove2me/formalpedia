-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_eq_8_0_redundant
-- name    : ManneLP.Equilibrium.eq_8_0_redundant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:11:18.83571+00:00
-- url     : https://prove2.me/theorems/b64c9482-13a1-4f2f-8a1f-fcf62c36b453
-- title:
--   §4, last paragraph — (8.0) is redundant: Σxᵢⱼ = 1 and (8.1)–(8.T) imply (8.0)
-- statement:
--   Consider Manne's inventory model with admissible pairs $A$ (so $i+j\le T$ for every $(i,j)\in A$) and demand law $(p_n)$, $\sum_np_n=1$. Let $(x_{ij})_{(i,j)\in A}$ be real numbers with
--   $$
--   \sum_{(i,j)\in A}x_{ij}=1
--   $$
--   that satisfy the equations (8.t), $\sum_j x_{tj}=\sum_{i+j-n=t}p_nx_{ij}$, for $t=1,\dots,T$. Then $x$ also satisfies (8.0):
--   $$
--   \sum_j x_{0j}=\sum_{\substack{i,j,n:\\ i+j-n\le 0}}p_nx_{ij}.
--   $$
--
--   This is why the linear program's constraint set consists of the non-negativity conditions, (4) and (8.1)–(8.T) only.
--
--   **Formalization Note** Non-negativity of $x$ is not assumed; the statement is the stronger one, and the paper's claim is its special case.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), p. 262 (PDF p. 5), §4, last paragraph

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem eq_8_0_redundant (M : Model) (x : ℕ × ℕ → ℝ)
    (h4 : ∑ a ∈ M.A, x a = 1) (h8 : ∀ t : ℕ, 1 ≤ t → t ≤ M.T → Eq8t M x t) :
    Eq80 M x := by sorry

end ManneLP.Equilibrium
