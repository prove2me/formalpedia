-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_3_8
-- name    : LiqProvision.Oligopoly.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:47.812995+00:00
-- url     : https://prove2.me/theorems/49ec2851-bd3a-4fe4-9aa5-419b96113ca3
-- title:
--   Theorem 3.8, p. 10 — the ODE (3.8) has a unique increasing, continuously differentiable solution on ℝ \ {0}
-- statement:
--   Assume the standing assumptions and Assumptions 2.1 and 3.7. Then there is a function $P_*'$ on $\mathbb R\setminus\{0\}$ that is increasing, continuously differentiable and solves the ODE (3.8) with nonvanishing denominators, and any two such functions agree on $\mathbb R\setminus\{0\}$.
--
--   There are no boundary conditions: monotonicity and finiteness on the whole line select the solution.
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. Functions are on $\mathbb R$, and their value at $0$ is ignored: uniqueness is agreement on $\mathbb R\setminus\{0\}$.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 10, Theorem 3.8; proof pp. 23–27

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem theorem_3_8 (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) :
    ∃ p : ℝ → ℝ, IsODESol M p ∧ ∀ q : ℝ → ℝ, IsODESol M q → Set.EqOn q p {0}ᶜ := by sorry
end LiqProvision.Oligopoly
