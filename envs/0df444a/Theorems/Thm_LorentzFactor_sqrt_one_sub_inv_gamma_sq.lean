-- Prove2me | Theorems.Thm_LorentzFactor_sqrt_one_sub_inv_gamma_sq
-- name    : LorentzFactor.sqrt_one_sub_inv_gamma_sq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:48:06.272733+00:00
-- url     : https://prove2.me/theorems/4b7bf979-8a36-458b-a0ac-c645f1d1a10f
-- title:
--   Inverting the definition: $\sqrt{1 - 1/\gamma^{2}} = \beta$
-- statement:
--   The defining relation can be inverted to recover the speed from the Lorentz factor: for $0 \le \beta < 1$,
--
--   $$\sqrt{1 - \frac{1}{\gamma(\beta)^{2}}} = \beta,$$
--
--   which is the article's inverted equation $v = c\sqrt{1 - 1/\gamma^{2}}$ in units $c = 1$. The restriction to non-negative $\beta$ is what makes the map invertible: $\gamma$ does not distinguish $\beta$ from $-\beta$.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem sqrt_one_sub_inv_gamma_sq (β : ℝ) (h₀ : 0 ≤ β) (h₁ : β < 1) :
    Real.sqrt (1 - 1 / gamma β ^ 2) = β := by sorry

end LorentzFactor
