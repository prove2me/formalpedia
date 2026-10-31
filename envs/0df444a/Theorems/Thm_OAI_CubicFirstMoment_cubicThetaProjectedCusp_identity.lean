-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_cubicThetaProjectedCusp_identity
-- name    : OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:50:52.509697+00:00
-- url     : https://prove2.me/theorems/7f24a579-d9c0-4d72-9b12-03fe8774882e
-- title:
--   OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity` of [lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaActualProjection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaActualProjection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped MatrixGroups Matrix`):
--
--   ```lean
--   lemma cubicThetaProjectedCusp_identity (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
--       (j : Fin 3) (p : CubicThetaPoint) :
--       cubicThetaNormalizedSeriesSection.val
--         (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))=
--         cubicThetaProjectedCuspMultiplier g hc j*
--           cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
--             (cubicThetaFullTranslation (g 1 1) • p).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.CubicThetaPoint` and `OAI.CubicFirstMoment.cubicThetaPoint_topology` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.cubicThetaFullPointAction` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.CubicThetaSection` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.cubicThetaFullTranslation` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.cubicThetaProjectedCuspMultiplier` and `OAI.CubicFirstMoment.cubicThetaProjectedCuspType` (definitions bundle `OAIQ096A012` of this split); `OAI.CubicFirstMoment.cubicThetaCuspExpansion` (definitions bundle `OAIQ096A023` of this split); `OAI.CubicFirstMoment.cubicThetaNormalizedSeriesSection` (definitions bundle `OAIQ096A026` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.omegaE` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.cubicThetaResidue_radial_voronoi` and `OAI.CubicFirstMoment.cubicThetaResidue_voronoi` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Theta/CubicThetaActualProjection.lean (declaration OAI.CubicFirstMoment.cubicThetaProjectedCusp_identity)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026

section

attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaProjectedCusp_identity (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (j : Fin 3) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))=
      cubicThetaProjectedCuspMultiplier g hc j*
        cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
          (cubicThetaFullTranslation (g 1 1) • p).val := by
  sorry

end CubicFirstMoment

end

end OAI
end
