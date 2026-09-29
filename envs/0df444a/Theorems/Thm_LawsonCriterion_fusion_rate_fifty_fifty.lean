-- Prove2me | Theorems.Thm_LawsonCriterion_fusion_rate_fifty_fifty
-- name    : LawsonCriterion.fusion_rate_fifty_fifty
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:57:22.013737+00:00
-- url     : https://prove2.me/theorems/48df9553-0d40-4902-976b-bbfc4a3ed29f
-- title:
--   Volumetric fusion rate of a 50-50 D-T mixture
-- statement:
--   In the optimal 50-50 deuterium-tritium mixture the two fuel densities are each half of the total ion density, $n_{\mathrm{d}} = n_{\mathrm{t}} = n/2$, so the volume rate of fusion reactions $f = n_{\mathrm{d}} n_{\mathrm{t}} \langle\sigma v\rangle$ becomes
--
--   $$f = \tfrac14 n^2 \langle\sigma v\rangle.$$
--
--   This is the algebraic identity behind the factor $1/4$ that propagates into every later form of the Lawson criterion.
-- source:
--   Lawson criterion, Wikipedia, revision 1367242125, https://en.wikipedia.org/w/index.php?title=Lawson_criterion&oldid=1367242125 - section "Extensions into nτE", the equation f = n_d n_t ⟨σv⟩ = (1/4) n² ⟨σv⟩; after J. D. Lawson, Proc. Phys. Soc. B 70 (1957) 6-10, doi:10.1088/0370-1301/70/1/303

import Mathlib
import Definitions.Def_LawsonDTPlasma

namespace LawsonCriterion

/-- **Milestone.** In the optimal 50-50 D-T mixture the two fuel densities are
`n / 2`, so the volumetric fusion rate is `f = n² ⟨σv⟩ / 4`.
-/
theorem fusion_rate_fifty_fifty (n sigmav : ℝ) :
    fusionRate (n / 2) (n / 2) sigmav = (1 / 4) * n ^ 2 * sigmav := by sorry

end LawsonCriterion
