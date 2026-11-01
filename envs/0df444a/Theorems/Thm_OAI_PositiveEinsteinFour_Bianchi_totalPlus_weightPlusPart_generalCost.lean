-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_totalPlus_weightPlusPart_generalCost
-- name    : OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:32:02.25089+00:00
-- url     : https://prove2.me/theorems/1d296ee5-bac0-41e6-a6fc-c628e914e0ca
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open Matrix TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem totalPlus_weightPlusPart_generalCost (A : Mat)
--       (hA : symmetric A) (ht : traceFree A) (a : Vec) (Z : Tensor)
--       (hz : Z.traceFree) (hb : Z.bianchi) :
--       hessianGram A (fun r => totalPlus r (weightPlusPart a Z)) =
--         -30 * ‖a‖ ^ 2 * generalGradientForm A Z
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Tensor`, `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.TraceHessian.Mat`, `OAI.PositiveEinsteinFour.TraceHessian.symmetric` and `OAI.PositiveEinsteinFour.TraceHessian.traceFree` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart`, `OAI.PositiveEinsteinFour.CurvatureContraction.generalGradientForm`, `OAI.PositiveEinsteinFour.Bianchi.Tensor.bianchi` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.traceFree` (definitions bundle `OAIQ091C007` of this split); `OAI.PositiveEinsteinFour.HighestHessian.hessianGram` and `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced` and `OAI_PositiveEinsteinFour_QuaternionFrame_projection_bound_of_weight_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Matrix TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem totalPlus_weightPlusPart_generalCost (A : Mat)
    (hA : symmetric A) (ht : traceFree A) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    hessianGram A (fun r => totalPlus r (weightPlusPart a Z)) =
      -30 * ‖a‖ ^ 2 * generalGradientForm A Z := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end

end OAI
end
