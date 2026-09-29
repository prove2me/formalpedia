-- Prove2me | Theorems.Thm_LorentzFactor_gamma_tanh
-- name    : LorentzFactor.gamma_tanh
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:20:39.533987+00:00
-- url     : https://prove2.me/theorems/ac1791eb-05a0-4e47-8a03-6d8c9ae0d3df
-- title:
--   Rapidity form: $\gamma(\tanh w) = \cosh w$ and $\gamma\beta = \sinh w$
-- statement:
--   Parametrize the velocity by the **rapidity** $w$ through $\beta = \tanh w$. Then the Lorentz factor and the product $\gamma\beta$ are the hyperbolic cosine and sine of the rapidity:
--
--   $$\gamma(\tanh w) = \cosh w, \qquad \gamma(\tanh w)\tanh w = \sinh w.$$
--
--   This is the alternative representation of $\gamma$ by rapidity given in the source article, and the reason the boost matrix is a hyperbolic rotation.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_tanh (w : ℝ) :
    gamma (Real.tanh w) = Real.cosh w ∧
      gamma (Real.tanh w) * Real.tanh w = Real.sinh w := by sorry

end LorentzFactor
