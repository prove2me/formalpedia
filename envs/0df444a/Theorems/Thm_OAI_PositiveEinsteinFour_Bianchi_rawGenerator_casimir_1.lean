-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_rawGenerator_casimir_1
-- name    : OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:17:34.009254+00:00
-- url     : https://prove2.me/theorems/58c173f5-459d-43ac-8b03-dd79f0b68f27
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1` of [lean/OAI/Geometry/EinsteinFour/GradientOperator.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientOperator.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian`):
--
--   ```lean
--   theorem rawGenerator_casimir_1 (Z : Tensor)
--       (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
--       (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 b) =
--         (-35 : ℝ) • Z.matrix 1 b
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Tensor`, `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.matrix` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.Tensor.bianchi` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.traceFree` (definitions bundle `OAIQ091C007` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientOperator.lean (declaration OAI.PositiveEinsteinFour.Bianchi.rawGenerator_casimir_1)

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

theorem rawGenerator_casimir_1 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 b) =
      (-35 : ℝ) • Z.matrix 1 b := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end OAI
end
