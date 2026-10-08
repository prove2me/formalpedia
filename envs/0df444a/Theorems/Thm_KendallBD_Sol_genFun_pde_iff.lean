-- Prove2me | Theorems.Thm_KendallBD_Sol_genFun_pde_iff
-- name    : KendallBD.Sol.genFun_pde_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:06.699573+00:00
-- url     : https://prove2.me/theorems/1aba340b-c39c-4c30-889f-0c0d71028b4a
-- title:
--   §2, (6), (9), p. 3 — PDE and equations for ξ, η
-- statement:
--   Let $\xi$ and $\eta$ be real functions differentiable at time $t$, with derivatives $\xi'$ and $\eta'$, and put
--   $$
--   \phi(z,t)=\frac{\xi(t)+(1-\xi(t)-\eta(t))z}{1-\eta(t)z}.
--   $$
--   For all real $z$ where $1-\eta(t)z\ne0$, the generating-function equation $\partial_t\phi=(z-1)(\lambda(t)z-\mu(t))\partial_z\phi$ holds exactly when
--   $$
--   (\eta\xi'-\xi\eta')+\eta'=\lambda(1-\xi)(1-\eta),\qquad
--   \xi'=\mu(1-\xi)(1-\eta)
--   $$
--   at $t$. This is the algebraic reduction on page 3.
--
--   **Formalization Note** The result uses arbitrary real rate functions at the chosen time; no sign or continuity hypothesis is needed for this pointwise algebraic statement. Derivatives in both variables are explicit `HasDerivAt` assertions.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (6), (9), p. 3

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem genFun_pde_iff (lam mu ξ η : ℝ → ℝ) (t ξ' η' : ℝ)
    (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t) :
    (∀ z : ℝ, η t * z ≠ 1 → ∀ a b : ℝ,
      HasDerivAt (fun s => genFun (ξ s) (η s) z) a t →
      HasDerivAt (fun y => genFun (ξ t) (η t) y) b z →
      a = (z - 1) * (lam t * z - mu t) * b) ↔
    ((η t * ξ' - ξ t * η') + η' = lam t * (1 - ξ t) * (1 - η t) ∧
      ξ' = mu t * (1 - ξ t) * (1 - η t)) := by sorry

end KendallBD.Sol
