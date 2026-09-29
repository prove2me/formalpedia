-- Prove2me | Theorems.Thm_LawsonCriterion_lawson_criterion
-- name    : LawsonCriterion.lawson_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:09:23.801993+00:00
-- url     : https://prove2.me/theorems/932bde46-1aca-4f81-9516-3f0aa8ab42bb
-- title:
--   Lawson criterion: $n\tau_E \ge 12T / (E_{\mathrm{ch}} \langle \sigma v\rangle)$
-- statement:
--   **Goal theorem.** For a steady-state 50-50 deuterium-tritium plasma whose fusion heating exceeds its losses, the product of the particle density and the energy confinement time is bounded below by a quantity depending only on the temperature, the charged-product energy and the reactivity:
--
--   $$n\,\tau_E \;\ge\; L \;\equiv\; \frac{12\,T}{E_{\mathrm{ch}}\,\langle\sigma v\rangle}.$$
--
--   This is equation (1) of the source, the Lawson criterion in its $n\tau_E$ form. The constant $12$ is $4 \cdot 3$: the $4$ from the 50-50 mixture, the $3$ from the ideal-gas energy density $W = 3nT$. Replacing $T/\langle\sigma v\rangle$ by its minimum over temperature - a step this mission does not formalize - turns the bound into the temperature-independent constant quoted for each fuel.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extensions into nτE", equation (1): nτ_E ≥ L ≡ 12T / (E_ch ⟨σv⟩); after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Goal theorem.** The Lawson criterion (equation (1)): a self-heating
steady-state D-T plasma satisfies `n τ_E ≥ 12 T / (E_ch ⟨σv⟩)`.
-/
theorem lawson_criterion (p : DTPlasma) (h : p.SelfHeating) :
    p.n * p.tauE ≥ 12 * p.T / (p.Ech * p.sigmav) := by sorry

end LawsonCriterion
