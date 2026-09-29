-- Prove2me | Theorems.Thm_LorentzFactor_alpha_eq_inv_gamma
-- name    : LorentzFactor.alpha_eq_inv_gamma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:50:30.668902+00:00
-- url     : https://prove2.me/theorems/eda42675-4914-4398-8bac-fd237215223c
-- title:
--   The reciprocal factor: $\alpha = 1/\gamma$
-- statement:
--   For $|\beta| < 1$ the quantity $\alpha(\beta) = \sqrt{1 - \beta^{2}}$ is the multiplicative inverse of the Lorentz factor: $\alpha(\beta) = \gamma(\beta)^{-1}$ and $\gamma(\beta)\,\alpha(\beta) = 1$. This is the reciprocal $1/\gamma$ tabulated in the third column of the article's table of numerical values, and the quantity some authors take as the primitive definition.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem alpha_eq_inv_gamma (β : ℝ) (h : |β| < 1) :
    alpha β = (gamma β)⁻¹ ∧ gamma β * alpha β = 1 := by sorry

end LorentzFactor
