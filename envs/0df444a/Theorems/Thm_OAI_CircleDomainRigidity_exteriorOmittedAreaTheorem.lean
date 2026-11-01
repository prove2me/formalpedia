-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_exteriorOmittedAreaTheorem
-- name    : OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T05:15:55.495758+00:00
-- url     : https://prove2.me/theorems/8c3afd02-e6d4-40e9-bfba-8f5716dcab6f
-- title:
--   OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem` of [lean/OAI/Analysis/CircleDomains/Sobolev/ExteriorAreaBoundProof.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/ExteriorAreaBoundProof.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Filter Function MeasureTheory Metric Bornology Asymptotics`, `open scoped Topology ENNReal`):
--
--   ```lean
--   lemma exteriorOmittedAreaTheorem (hsch : PlanarSchoenflies)
--       (hgreen : UnorientedFiniteCircleGreenFormula) : ExteriorOmittedAreaTheorem
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PlanarSchoenflies` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorOmittedAreaTheorem` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` (definitions bundle `Q146C005` of this split).
--
--   **Used by.** The proof of `OAI.Problem047.removability_implies_rigidity` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Sobolev/ExteriorAreaBoundProof.lean (declaration OAI.CircleDomainRigidity.exteriorOmittedAreaTheorem)

import Mathlib
import Definitions.Def_Q146C005

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Function MeasureTheory Metric Bornology Asymptotics
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exteriorOmittedAreaTheorem (hsch : PlanarSchoenflies)
    (hgreen : UnorientedFiniteCircleGreenFormula) : ExteriorOmittedAreaTheorem := by
  sorry

end CircleDomainRigidity

end

end OAI
end
