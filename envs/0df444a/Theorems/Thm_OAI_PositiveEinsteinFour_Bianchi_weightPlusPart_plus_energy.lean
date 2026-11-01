-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_weightPlusPart_plus_energy
-- name    : OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:35:23.072927+00:00
-- url     : https://prove2.me/theorems/e5b24a42-177b-419c-b8be-f3d3a54a77db
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy` of [lean/OAI/Geometry/EinsteinFour/RealVectorCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/RealVectorCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian HighestHessian`):
--
--   ```lean
--   theorem weightPlusPart_plus_energy (a : Vec) (Z : Tensor)
--       (hz : Z.traceFree) (hb : Z.bianchi) :
--       (∑ s : Fin 3, hessianNormSq (totalPlus s (weightPlusPart a Z))) =
--         48 * hessianNormSq (weightPlusPart a Z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Tensor` and `OAI.PositiveEinsteinFour.Bianchi.Vec` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.bianchi` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.traceFree` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.TraceHessian.hessianNormSq` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced` and `OAI_PositiveEinsteinFour_QuaternionFrame_projection_bound_of_weight_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/RealVectorCost.lean (declaration OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy)

import Mathlib
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian HighestHessian

theorem weightPlusPart_plus_energy (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, hessianNormSq (totalPlus s (weightPlusPart a Z))) =
      48 * hessianNormSq (weightPlusPart a Z) := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end OAI
end
