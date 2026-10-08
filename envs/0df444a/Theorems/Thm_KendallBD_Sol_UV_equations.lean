-- Prove2me | Theorems.Thm_KendallBD_Sol_UV_equations
-- name    : KendallBD.Sol.UV_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:06.289274+00:00
-- url     : https://prove2.me/theorems/58544bfe-1249-46a4-b476-096795ff72e4
-- title:
--   §2, p. 3 — equations for U and V
-- statement:
--   Suppose differentiable functions $\xi,\eta$ satisfy Kendall’s paired equations at time $t$, and $U(t)=1-\xi(t)\ne0$. With $U=1-\xi$ and $V=1-\eta$, their derivatives satisfy
--   $$
--   U'=-\mu VU,\qquad V'=(\mu-\lambda)V-\mu V^2.
--   $$
--   These are the equations preceding the substitution $W=1/V$.
--
--   **Formalization Note** The first equation is multiplied out from the printed $U'/U=-\mu V$, with the explicit nonzero condition needed to infer the $V$ equation. For Kendall’s solution, $U=e^{-\rho}/W>0$ at each finite nonnegative time.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, displays following (9), p. 3

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem UV_equations (lam mu ξ η : ℝ → ℝ) (t ξ' η' : ℝ)
    (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t)
    (hU : 1 - ξ t ≠ 0)
    (hpair : (η t * ξ' - ξ t * η') + η' = lam t * (1 - ξ t) * (1 - η t) ∧
      ξ' = mu t * (1 - ξ t) * (1 - η t)) :
    -ξ' = -mu t * (1 - η t) * (1 - ξ t) ∧
      -η' = (mu t - lam t) * (1 - η t) - mu t * (1 - η t) ^ 2 := by sorry

end KendallBD.Sol
