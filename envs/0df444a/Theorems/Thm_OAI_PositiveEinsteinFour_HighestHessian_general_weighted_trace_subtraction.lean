-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_weighted_trace_subtraction
-- name    : OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:57:18.952035+00:00
-- url     : https://prove2.me/theorems/d13cfc6c-b0d7-4ae4-8a07-caefe6d270f1
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem general_weighted_trace_subtraction (A U M : Mat)
--       (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
--       (hM : symmetric M) (htM : traceFree M)
--       (X L : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
--       (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) (m : ℝ) :
--       m * generalCurvaturePairing A U (X - traceComponent M) (X - traceComponent M) +
--           generalCurvaturePairing A U (X - traceComponent M) L =
--         m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X L -
--           m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) -
--             generalCurvaturePairing A U (traceComponent M) L
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.TraceHessian.Hessian`, `OAI.PositiveEinsteinFour.TraceHessian.Mat`, `OAI.PositiveEinsteinFour.TraceHessian.symmetric` and `OAI.PositiveEinsteinFour.TraceHessian.traceFree` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.divergence` (definitions bundle `OAIQ091C008` of this split); `OAI.PositiveEinsteinFour.TraceHessian.hessianTrace` and `OAI.PositiveEinsteinFour.TraceHessian.traceComponent` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian` and `OAI_PositiveEinsteinFour_HighestHessian_general_local_weighted_original_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction)

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

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem general_weighted_trace_subtraction (A U M : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A)
    (hM : symmetric M) (htM : traceFree M)
    (X L : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) (m : ℝ) :
    m * generalCurvaturePairing A U (X - traceComponent M) (X - traceComponent M) +
        generalCurvaturePairing A U (X - traceComponent M) L =
      m * generalCurvaturePairing A U X X + generalCurvaturePairing A U X L -
        m * generalCurvaturePairing A U (traceComponent M) (traceComponent M) -
          generalCurvaturePairing A U (traceComponent M) L := by
  sorry

end
end PositiveEinsteinFour.HighestHessian
end

end OAI
end
