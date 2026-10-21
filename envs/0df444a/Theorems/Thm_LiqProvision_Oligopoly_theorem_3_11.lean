-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_3_11
-- name    : LiqProvision.Oligopoly.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:53.100541+00:00
-- url     : https://prove2.me/theorems/2868a427-76df-431e-9b20-1c5fe79e902a
-- title:
--   Theorem 3.11, p. 11 — P∗(n) = ∫₀ⁿ P′∗ is the unique symmetric Nash equilibrium for K dealers
-- statement:
--   Assume the standing assumptions ($K\ge2$ dealers, $\gamma_c>0$, $\gamma_d\ge0$, positive probability densities $f_S$, $f_M$), Assumption 2.1 (log-concavity), Assumption 3.7 ($\limsup_{w\to\pm\infty}g'(w)<1$), and let $P_*'$ be the increasing, continuously differentiable solution of the ODE (3.8) on $\mathbb R\setminus\{0\}$, satisfying Assumption 3.10. Then, for every function $P:\mathbb R\to\mathbb R$,
--   $$P\ \text{is a symmetric Nash equilibrium for $K$ dealers}\iff P(n)=\int_0^nP_*'(x)\,dx\ \text{ for all }n\in\mathbb R .$$
--   That is, $P_*(n)=\int_0^nP_*'(x)\,dx$ is a symmetric Nash equilibrium, and it is the only one.
--
--   This is the main result of the paper: competition between $K$ dealers who quote price schedules to clients with private information and inventory costs has exactly one symmetric equilibrium, whose marginal prices solve the nonlinear ODE (3.8).
--
--   **Formalization Note.**
--   1. "Let $P_*'$ be the solution of the ODE (3.8) from Theorem 3.8" is read as: for every $p$ in Theorem 3.8's class. By Theorem 3.8 that class is nonempty and its members agree off $0$, so this is the same statement; it is not vacuous.
--   2. Symmetric Nash equilibrium is the predicate of the model file: $P$ admissible, and no $P_1$ for which $(P_1,P,\dots,P)$ is compatible gives dealer 1 a larger goal functional (with the $-\infty$ convention of footnote 5). Deviations are not restricted further.
--   3. Assumption 3.10 is stated about the same $p$, with (3.10) in the form $(-\bar F/f)'-g'\le\gamma_d/\gamma_c$ on $[p(0+),\infty)$. The page prints $(\bar F/f)'$, a condition that always holds; the proof ((B.57), p. 28) uses the form with the minus sign.
--   4. The standing assumptions $K\ge2$ (p. 9), $\gamma_c>0$ (p. 3), $\gamma_d\ge0$ (p. 7) and positive probability densities (Assumption 2.1) are hypotheses.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 11, Theorem 3.11; proof pp. 27–30

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem theorem_3_11 (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) (p : ℝ → ℝ) (hp : IsODESol M p) (h310 : Assumption310 M p)
    (P : ℝ → ℝ) :
    IsSymNE M P ↔ ∀ n, P n = ∫ x in (0 : ℝ)..n, p x := by sorry
end LiqProvision.Oligopoly
