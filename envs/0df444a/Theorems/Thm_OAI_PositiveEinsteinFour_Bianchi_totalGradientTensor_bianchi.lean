-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalGradientTensor_bianchi
-- name    : OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:06:22.663132+00:00
-- url     : https://prove2.me/theorems/a53b5165-b779-480c-a84e-865e77e84496
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi` of [lean/OAI/Geometry/EinsteinFour/WeylLaplacian.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylLaplacian.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian`):
--
--   ```lean
--   theorem totalGradientTensor_bianchi (s : Fin 3) (Z : Tensor)
--       (hz : Z.traceFree) (hb : Z.bianchi) : (totalGradientTensor s Z).bianchi
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Tensor` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.bianchi` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.traceFree` (definitions bundle `OAIQ091C007` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost` and `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylLaplacian.lean (declaration OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi)

import Mathlib
import Definitions.Def_OAIQ091C007

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
open TraceHessian

theorem totalGradientTensor_bianchi (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) : (totalGradientTensor s Z).bianchi := by
  sorry

end

end PositiveEinsteinFour.Bianchi

end OAI
end
