-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_proposition_3_1
-- name    : LiqProvision.Oligopoly.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:36.668981+00:00
-- url     : https://prove2.me/theorems/355fe29d-b990-43eb-acff-f9b2cc6b55fb
-- title:
--   Proposition 3.1, p. 7 — the conditional mean g(y) = E[V | Y = y] is C¹ with 0 < g′ < 1
-- statement:
--   Let the signal density $f_S$ and the inventory density $f_M$ be positive, log-concave probability densities (Assumption 2.1), and let $\gamma_c>0$. Then the conditional mean of the asset payoff given the client's effective type $Y=S-\gamma_cM$,
--   $$y\mapsto g(y)=E[V\mid Y=y],$$
--   is continuously differentiable and
--   $$0<g'(y)<1\qquad\text{for all }y\in\mathbb R .$$
--
--   The bounds mean that the client's type is positively but imperfectly informative about the payoff; they are the basic input of the ODE (3.8).
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. Only $\gamma_c>0$ and the density conditions are assumed: the statement does not involve $K$ or $\gamma_d$.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 7, Proposition 3.1, (3.2)

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem proposition_3_1 (M : Params) (hγc : 0 < M.γc) (hS : IsDensity M.fS)
    (hM : IsDensity M.fM) (h21 : M.Assumption21) :
    ContDiff ℝ 1 (condMean M) ∧
      ∀ y, 0 < deriv (condMean M) y ∧ deriv (condMean M) y < 1 := by sorry
end LiqProvision.Oligopoly
