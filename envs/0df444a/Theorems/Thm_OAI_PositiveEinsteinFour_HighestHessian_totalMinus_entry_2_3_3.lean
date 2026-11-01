-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalMinus_entry_2_3_3
-- name    : OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:23:02.111383+00:00
-- url     : https://prove2.me/theorems/6b69d59a-0920-4a87-bc06-bb1214ec8297
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3` of [lean/OAI/Geometry/EinsteinFour/HighestMinusCoordinates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestMinusCoordinates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Bianchi TraceHessian`):
--
--   ```lean
--   theorem totalMinus_entry_2_3_3 (c : Fin 21 → ℝ) :
--       totalMinus 2 (highest c) 3 3 = highest (minusCoordinates 2 c) 3 3
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.HighestHessian.highest` and `OAI.PositiveEinsteinFour.TraceHessian.Mat` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.minusCoordinates` (definitions bundle `OAIQ091C003` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalMinus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestMinusCoordinates.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3)

import Mathlib
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem totalMinus_entry_2_3_3 (c : Fin 21 → ℝ) :
    totalMinus 2 (highest c) 3 3 = highest (minusCoordinates 2 c) 3 3 := by
  sorry

end
end PositiveEinsteinFour.HighestHessian

end OAI
end
