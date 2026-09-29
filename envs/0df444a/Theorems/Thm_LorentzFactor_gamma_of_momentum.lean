-- Prove2me | Theorems.Thm_LorentzFactor_gamma_of_momentum
-- name    : LorentzFactor.gamma_of_momentum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:24:09.014931+00:00
-- url     : https://prove2.me/theorems/24e7eaf0-3166-44ec-bbd2-b6bf8bce2ad6
-- title:
--   Momentum form: $\gamma = \sqrt{1 + (p/mc)^2}$
-- statement:
--   Let a particle of rest mass $m > 0$ move with velocity ratio $\beta$, $|\beta| < 1$, and let $p = \gamma(\beta)\, m \beta$ be its relativistic momentum (in units $c = 1$). Then the Lorentz factor is recovered from the momentum by
--
--   $$\gamma = \sqrt{1 + \left(\frac{p}{m}\right)^{2}},$$
--
--   the momentum representation of $\gamma$ listed under *Alternative representations* in the source article.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_of_momentum (β m p : ℝ) (hβ : |β| < 1) (hm : 0 < m)
    (hp : p = gamma β * m * β) :
    gamma β = Real.sqrt (1 + (p / m) ^ 2) := by sorry

end LorentzFactor
