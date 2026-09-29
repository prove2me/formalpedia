-- Prove2me | Theorems.Thm_LawsonCriterion_self_heating_substituted
-- name    : LawsonCriterion.self_heating_substituted
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:05:37.628845+00:00
-- url     : https://prove2.me/theorems/1a3fd03f-4d06-47c3-bfca-a90a69809e87
-- title:
--   The self-heating condition with all quantities substituted
-- statement:
--   Lawson's requirement is that fusion heating exceed the losses, $f E_{\mathrm{ch}} \ge P_{\mathrm{loss}}$. Substituting the 50-50 reaction rate $f = \tfrac14 n^2 \langle\sigma v\rangle$ on the left and the loss density $P_{\mathrm{loss}} = 3nT/\tau_E$ on the right turns it into an inequality between explicit functions of the plasma parameters:
--
--   $$\tfrac14 n^2 \langle\sigma v\rangle E_{\mathrm{ch}} \;\ge\; \frac{3nT}{\tau_E}.$$
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extensions into nτE", the inequality (1/4) n² ⟨σv⟩ E_ch ≥ 3nT / τ_E; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** Substituting the known quantities into `f E_ch ≥ P_loss`
yields `(1/4) n² ⟨σv⟩ E_ch ≥ 3 n T / τ_E`.
-/
theorem self_heating_substituted (p : DTPlasma) (h : p.SelfHeating) :
    (1 / 4) * p.n ^ 2 * p.sigmav * p.Ech ≥ 3 * p.n * p.T / p.tauE := by sorry

end LawsonCriterion
