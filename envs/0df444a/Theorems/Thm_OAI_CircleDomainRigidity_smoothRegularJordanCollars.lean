-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_smoothRegularJordanCollars
-- name    : OAI.CircleDomainRigidity.smoothRegularJordanCollars
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T05:39:05.352694+00:00
-- url     : https://prove2.me/theorems/5eb23baa-b996-454a-910d-ecd4bd1b69f0
-- title:
--   OAI.CircleDomainRigidity.smoothRegularJordanCollars: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.smoothRegularJordanCollars` of [lean/OAI/Analysis/CircleDomains/Topology/RegularJordanCollarProof.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Topology/RegularJordanCollarProof.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter`, `open scoped Topology ContDiff NNReal`):
--
--   ```lean
--    theorem smoothRegularJordanCollars
--       (hgreen : UnorientedFiniteCircleGreenFormula) :
--       SmoothRegularJordanCollars
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.SmoothRegularJordanCollars` (definitions bundle `Q146C010` of this split).
--
--   **Used by.** The proofs of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity` of this split import it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Topology/RegularJordanCollarProof.lean (declaration OAI.CircleDomainRigidity.smoothRegularJordanCollars)

import Mathlib
import Definitions.Def_Q146C010

section

attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smoothRegularJordanCollars
    (hgreen : UnorientedFiniteCircleGreenFormula) :
    SmoothRegularJordanCollars := by
  sorry

end CircleDomainRigidity

end

end OAI
end
