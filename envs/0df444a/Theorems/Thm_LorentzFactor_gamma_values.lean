-- Prove2me | Theorems.Thm_LorentzFactor_gamma_values
-- name    : LorentzFactor.gamma_values
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:26:18.754288+00:00
-- url     : https://prove2.me/theorems/70eb7cd9-cb42-4fb1-8d25-ad43994bb2e7
-- title:
--   Exact table entries: $\gamma(0)=1$, $\gamma(3/5)=5/4$, $\gamma(4/5)=5/3$, $\gamma(\sqrt3/2)=2$
-- statement:
--   The exact entries of the article's table of numerical values:
--
--   $$\gamma(0) = 1, \quad \gamma(0.6) = 1.25, \quad \gamma(0.8) = \tfrac{5}{3}, \quad \gamma\!\left(\tfrac{\sqrt3}{2}\right) = 2.$$
--
--   The first three are the rows the article marks as exact; the fourth is the exact value behind the row $\beta \approx 0.866$, $\gamma = 2$.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_values :
    gamma 0 = 1 ∧ gamma (3 / 5) = 5 / 4 ∧ gamma (4 / 5) = 5 / 3 ∧
      gamma (Real.sqrt 3 / 2) = 2 := by sorry

end LorentzFactor
