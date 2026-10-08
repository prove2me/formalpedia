-- Prove2me | Theorems.Thm_KendallBD_Sol_W_ode
-- name    : KendallBD.Sol.W_ode
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:26:01.551121+00:00
-- url     : https://prove2.me/theorems/8d145dbe-8810-42d4-aec3-479469651a0b
-- title:
--   §2, (10a)–(11), pp. 3–4 — W solves its linear equation
-- statement:
--   For continuous real rate functions $\lambda,\mu$, let $\rho(t)=\int_0^t(\mu-\lambda)$ and
--   $$
--   W(t)=e^{-\rho(t)}\left(1+\int_0^t e^{\rho(\tau)}\mu(\tau)\,d\tau\right).
--   $$
--   Then $W(0)=1$ and, at every real $t$,
--   $$
--   W'(t)+(\mu(t)-\lambda(t))W(t)=\mu(t).
--   $$
--   This is the integrating-factor formula and differential equation on pages 3–4.
--
--   **Formalization Note** No nonnegativity assumption is needed for this identity; continuity ensures the derivatives of the integrals exist.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (10a)–(11), pp. 3–4

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem W_ode (lam mu : ℝ → ℝ) (hlam : Continuous lam)
    (hmu : Continuous mu) :
    W lam mu 0 = 1 ∧
      ∀ t : ℝ, HasDerivAt (W lam mu)
        (mu t - (mu t - lam t) * W lam mu t) t := by sorry

end KendallBD.Sol
