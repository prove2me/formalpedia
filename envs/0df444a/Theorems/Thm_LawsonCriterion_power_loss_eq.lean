-- Prove2me | Theorems.Thm_LawsonCriterion_power_loss_eq
-- name    : LawsonCriterion.power_loss_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:58:45.036392+00:00
-- url     : https://prove2.me/theorems/9fc253bf-aca1-4b6e-84ea-8164cb6173e6
-- title:
--   Power loss density in terms of the energy confinement time
-- statement:
--   The energy confinement time is defined as the energy density divided by the power loss density, $\tau_E = W / P_{\mathrm{loss}}$, and for a plasma in which electrons and ions share the temperature $T$ the ideal gas law gives $W = 3nT$. Since all the quantities involved are strictly positive, this definition can be read backwards: the power lost per unit volume is
--
--   $$P_{\mathrm{loss}} = \frac{3nT}{\tau_E}.$$
--
--   This is the form in which the loss term enters Lawson's inequality.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extensions into nτE", the equation τ_E = W / P_loss with W = 3nT; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** The definition `τ_E = W / P_loss` of the energy confinement
time, with `W = 3 n T`, inverts to `P_loss = 3 n T / τ_E`.
-/
theorem power_loss_eq (p : DTPlasma) : p.Ploss = 3 * p.n * p.T / p.tauE := by sorry

end LawsonCriterion
