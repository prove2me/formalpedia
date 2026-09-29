-- Prove2me | Theorems.Thm_LorentzFactor_gamma_sub_one_div_sq_tendsto
-- name    : LorentzFactor.gamma_sub_one_div_sq_tendsto
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:24:27.948043+00:00
-- url     : https://prove2.me/theorems/2485a4bf-905d-4d93-aaf1-41c452358035
-- title:
--   Low-speed limit: $(\gamma - 1)/\beta^{2} \to 1/2$
-- statement:
--   The leading term of the Maclaurin series $\gamma = 1 + \tfrac{1}{2}\beta^{2} + \tfrac{3}{8}\beta^{4} + \cdots$ is captured by the limit
--
--   $$\lim_{\beta \to 0,\ \beta \ne 0} \frac{\gamma(\beta) - 1}{\beta^{2}} = \frac{1}{2}.$$
--
--   Multiplying by $mc^{2}$, this is the statement that the relativistic kinetic energy $(\gamma - 1)mc^{2}$ reduces to the Newtonian $\tfrac{1}{2}mv^{2}$ at low speed, the reduction discussed in the article's series-expansion section.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_sub_one_div_sq_tendsto :
    Tendsto (fun β : ℝ => (gamma β - 1) / β ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by sorry

end LorentzFactor
