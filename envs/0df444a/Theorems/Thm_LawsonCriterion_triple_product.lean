-- Prove2me | Theorems.Thm_LawsonCriterion_triple_product
-- name    : LawsonCriterion.triple_product
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:11:08.68684+00:00
-- url     : https://prove2.me/theorems/4228ce11-b22b-4797-b094-8a07b7e53f44
-- title:
--   Triple product form: $nT\tau_E \ge (12/E_{\mathrm{ch}})\,T^2/\langle\sigma v\rangle$
-- statement:
--   Multiplying the Lawson criterion by the temperature gives the figure of merit actually reported by experiments, the *triple product* of density, temperature and confinement time:
--
--   $$n\,T\,\tau_E \;\ge\; \frac{12}{E_{\mathrm{ch}}}\,\frac{T^2}{\langle\sigma v\rangle}.$$
--
--   The quantity $T^2/\langle\sigma v\rangle$ on the right, like $T/\langle\sigma v\rangle$ before it, has an absolute minimum in temperature - for D-T near $14$ keV, slightly below the temperature that minimises the $n\tau_E$ bound.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extension into the triple product", the inequality nTτ_E ≥ (12 / E_ch) T² / ⟨σv⟩; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** The triple product form of the criterion:
`n T τ_E ≥ (12 / E_ch) (T² / ⟨σv⟩)`.
-/
theorem triple_product (p : DTPlasma) (h : p.SelfHeating) :
    p.n * p.T * p.tauE ≥ (12 / p.Ech) * (p.T ^ 2 / p.sigmav) := by sorry

end LawsonCriterion
