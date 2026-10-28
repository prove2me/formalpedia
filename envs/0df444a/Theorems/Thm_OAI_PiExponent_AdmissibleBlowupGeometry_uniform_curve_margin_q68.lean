-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleBlowupGeometry_uniform_curve_margin_q68
-- name    : OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:47:36.062476+00:00
-- url     : https://prove2.me/theorems/15cdaced-3fa2-45f8-89be-7b1eadea911b
-- title:
--   OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin` of [lean/OAI/NumberTheory/PiExponent/Geometry/AdmissibleCurveDegreeData.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/AdmissibleCurveDegreeData.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.AdmissibleBlowupGeometry`, with `open AlgebraicGeometry`):
--
--   ```lean
--   theorem uniform_curve_margin_q68 :
--       ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
--         uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
--           (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.AdmissibleParameters` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.NumericalAmpleness.IntegralCurve` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.blowup` (definitions bundle `OAIQ068A020` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.structureMap` and `OAI.PiExponent.NumericalAmpleness.curveDegree` (definitions bundle `OAIQ068A029` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.H`, `OAI.PiExponent.AdmissibleBlowupGeometry.interpolationBundle` and `OAI.PiExponent.AdmissibleBlowupGeometry.uniformMargin` (definitions bundle `OAIQ068A040` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/AdmissibleCurveDegreeData.lean (declaration OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A040

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem uniform_curve_margin_q68 :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) := by
  sorry

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end
