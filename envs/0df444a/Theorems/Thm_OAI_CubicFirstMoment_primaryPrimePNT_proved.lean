-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_primaryPrimePNT_proved
-- name    : OAI.CubicFirstMoment.primaryPrimePNT_proved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:03:06.439038+00:00
-- url     : https://prove2.me/theorems/c1d48fbf-d4c7-4a85-a513-b8ffad3dc2c5
-- title:
--   OAI.CubicFirstMoment.primaryPrimePNT_proved: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.primaryPrimePNT_proved` of [lean/OAI/NumberTheory/CubicMoment/Estimates/PrimaryPrimePNTProof.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimaryPrimePNTProof.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Topology Asymptotics`):
--
--   ```lean
--   theorem primaryPrimePNT_proved : PrimaryPrimePNT
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.PrimaryPrimePNT` (definitions bundle `OAIQ096A007` of this split).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.cubicTheta_primeProductGaussTail_isLittleO`, `OAI.CubicFirstMoment.cubicTheta_primeProductLowHeight_isLittleO` and `OAI.CubicFirstMoment.patterson_firstMoment` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PrimaryPrimePNTProof.lean (declaration OAI.CubicFirstMoment.primaryPrimePNT_proved)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ096A007

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Asymptotics
namespace CubicFirstMoment

theorem primaryPrimePNT_proved : PrimaryPrimePNT := by
  sorry

end CubicFirstMoment

end

end OAI
end
