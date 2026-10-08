-- Prove2me | Theorems.Thm_KendallBD_Sol_W_alt_forms
-- name    : KendallBD.Sol.W_alt_forms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:37.904826+00:00
-- url     : https://prove2.me/theorems/af3b5238-d11e-4d1e-a163-518cb907c634
-- title:
--   §2, (10b)–(10c), p. 4 — alternate formulas for W
-- statement:
--   For continuous rates $\lambda,\mu$ and $t\ge0$, Kendall’s $W$ also satisfies
--   $$
--   W(t)=1+e^{-\rho(t)}\int_0^t e^{\rho(\tau)}\lambda(\tau)\,d\tau,
--   $$
--   and
--   $$
--   W(t)=\tfrac12(1+e^{-\rho(t)})+\tfrac12e^{-\rho(t)}\int_0^t e^{\rho(\tau)}(\lambda(\tau)+\mu(\tau))\,d\tau.
--   $$
--   These are exactly the two alternate expressions in equations (10b) and (10c).
--
--   **Formalization Note** The equalities require continuity but no sign assumption. They are restricted to the paper’s time domain $t\ge0$.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (10b)–(10c), p. 4

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem W_alt_forms (lam mu : ℝ → ℝ) (hlam : Continuous lam)
    (hmu : Continuous mu) :
    ∀ t : ℝ, 0 ≤ t →
      W lam mu t = 1 + Real.exp (-rho lam mu t) *
        (∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * lam τ) ∧
      W lam mu t = (1 + Real.exp (-rho lam mu t)) / 2 +
        Real.exp (-rho lam mu t) / 2 *
        (∫ τ in (0 : ℝ)..t, Real.exp (rho lam mu τ) * (lam τ + mu τ)) := by sorry

end KendallBD.Sol
