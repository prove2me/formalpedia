-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_3_11_existence
-- name    : LiqProvision.Oligopoly.theorem_3_11_existence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T22:42:15.978773+00:00
-- url     : https://prove2.me/theorems/e37ce1cf-abd7-4720-9947-e3acd7f88fd9
-- title:
--   Theorem 3.11 (existence part), pp. 11, 27–30 — P∗(n) = ∫₀ⁿ P′∗ is a symmetric Nash equilibrium for K dealers
-- statement:
--   This is the existence (verification) half of Theorem 3.11: the price schedule built from the solution of the ODE (3.8) is a symmetric Nash equilibrium.
--
--   Assume the standing assumptions ($K\ge2$ dealers, client inventory cost $\gamma_c>0$, dealer inventory cost $\gamma_d\ge0$, positive probability densities $f_S$ of the signal and $f_M$ of the client's inventory), Assumption 2.1 (log-concavity of $f_S$ and $f_M$) and Assumption 3.7 ($\limsup_{w\to\pm\infty}g'(w)<1$ for the conditional mean $g(y)=E[V\mid Y=y]$). Let $P_*'$ be an increasing, continuously differentiable solution of the ODE (3.8) on $\mathbb R\setminus\{0\}$ (the class of Theorem 3.8) that satisfies Assumption 3.10. Then the price schedule
--   $$P_*(n)=\int_0^n P_*'(x)\,dx,\qquad n\in\mathbb R,$$
--   is a symmetric Nash equilibrium for $K$ dealers. That is, $P_*$ is admissible, and for every schedule $P_1$ for which $(P_1,P_*,\dots,P_*)$ is compatible, dealer 1's expected profit under the deviation $P_1$ (with the client's optimal response) does not exceed her expected profit under $(P_*,\dots,P_*)$.
--
--   Together with Lemma 3.6 and Theorem 3.8, which show that every symmetric Nash equilibrium has marginal prices solving (3.8), this gives the "unique symmetric Nash equilibrium" statement of Theorem 3.11. The paper's proof of Theorem 3.11 (pp. 27–30) is precisely the verification of this statement, via the representation (B.50) and the pointwise optimality (B.53)–(B.54).
--
--   **Formalization Note.** The model objects (admissibility, compatibility, the dealer goal functional with the $-\infty$ convention of footnote 5, symmetric Nash equilibrium, the ODE (3.8) and Assumption 3.10 in the form used in (B.57)) are those of the definition file `LiqProvision_Oligopoly_Model`, exactly as in the mission's goal theorem `LiqProvision.Oligopoly.theorem_3_11`. This statement is the special case $P=P_*$ of the goal's "⇐" direction.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 11, Theorem 3.11 (existence of the equilibrium); proof pp. 27–30

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem theorem_3_11_existence (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) (p : ℝ → ℝ) (hp : IsODESol M p) (h310 : Assumption310 M p) :
    IsSymNE M (fun n => ∫ x in (0 : ℝ)..n, p x) := by sorry
end LiqProvision.Oligopoly
