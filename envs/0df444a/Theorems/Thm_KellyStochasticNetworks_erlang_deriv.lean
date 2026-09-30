-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_deriv
-- name    : KellyStochasticNetworks.erlang_deriv
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T05:49:53.236596+00:00
-- url     : https://prove2.me/theorems/64ecc64a-2214-4f98-af48-53dee49ba1b0
-- title:
--   Exercise 1.8 — the derivative of Erlang's formula in the traffic intensity
-- statement:
--   Erlang's formula
--   $$E(\nu, C) = \frac{\nu^{C}/C!}{\sum_{j=0}^{C} \nu^{j}/j!}$$
--   is a differentiable function of the traffic intensity $\nu > 0$, and for $C \ge 1$ its
--   derivative is
--   $$\frac{d}{d\nu} E(\nu, C) = -\bigl(1 - E(\nu, C)\bigr)\bigl(E(\nu, C) - E(\nu, C-1)\bigr).$$
--
--   Since $E(\nu, C) < E(\nu, C-1)$ and $E(\nu, C) < 1$, the right-hand side is positive: blocking
--   increases with offered load. The identity is also the analytic form of the recursion by which
--   $E(\nu,C)$ is evaluated in practice, since it expresses the derivative at $C$ using only the
--   values at $C$ and $C-1$ rather than the sums that define them.
--
--   **Formalization Note** The restriction $C \ge 1$ is expressed by stating the result at $C+1$
--   for an arbitrary natural number $C$, so that $C-1$ never has to be interpreted by truncated
--   subtraction. Differentiability is asserted together with the value of the derivative, as a
--   single `HasDerivAt` statement at the point $\nu$.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 20 (PDF p. 28), Exercise 1.8: 'Show that d/dnu E(nu,C) = -(1 - E(nu,C))(E(nu,C) - E(nu,C-1)).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

namespace KellyStochasticNetworks

theorem erlang_deriv (ν : ℝ) (C : ℕ) (hν : 0 < ν) :
    HasDerivAt (fun v : ℝ => erlang v (C + 1))
      (-(1 - erlang ν (C + 1)) * (erlang ν (C + 1) - erlang ν C)) ν := by sorry

end KellyStochasticNetworks
