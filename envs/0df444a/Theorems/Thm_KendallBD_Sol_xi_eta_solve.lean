-- Prove2me | Theorems.Thm_KendallBD_Sol_xi_eta_solve
-- name    : KendallBD.Sol.xi_eta_solve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:42.380386+00:00
-- url     : https://prove2.me/theorems/7c8ba4db-e583-44d3-9d8f-838ab58ff04b
-- title:
--   §2, (12), p. 4 — ξ and η solve the coupled equations
-- statement:
--   Let $\lambda,\mu$ be continuous, nonnegative rates and define $\xi_t=1-e^{-\rho(t)}/W(t)$ and $\eta_t=1-1/W(t)$. Then $\xi_0=\eta_0=0$, and for every $t\ge0$ both functions are differentiable with derivatives satisfying
--   $$
--   (\eta\xi'-\xi\eta')+\eta'=\lambda(1-\xi)(1-\eta),\qquad
--   \xi'=\mu(1-\xi)(1-\eta).
--   $$
--   Thus Kendall’s explicit expressions (12) satisfy the equations derived from the generating-function PDE.
--
--   **Formalization Note** Nonnegative death rates ensure $W(t)>0$ on nonnegative times, so both divisions in (12) are genuine.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (12), p. 4

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem xi_eta_solve (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) :
    xi lam mu 0 = 0 ∧ eta lam mu 0 = 0 ∧
      ∀ t, 0 ≤ t → ∃ ξ' η' : ℝ,
        HasDerivAt (xi lam mu) ξ' t ∧ HasDerivAt (eta lam mu) η' t ∧
        (eta lam mu t * ξ' - xi lam mu t * η') + η' =
          lam t * (1 - xi lam mu t) * (1 - eta lam mu t) ∧
        ξ' = mu t * (1 - xi lam mu t) * (1 - eta lam mu t) := by sorry

end KendallBD.Sol
