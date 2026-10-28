-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveCycle_tensor_euler_margin_q68
-- name    : OAI.PiExponent.CurveCycle.tensor_euler_margin_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:39:51.607355+00:00
-- url     : https://prove2.me/theorems/539a0a5f-0732-4a36-b577-fb074ca695cf
-- title:
--   OAI.PiExponent.CurveCycle.tensor_euler_margin_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveCycle.tensor_euler_margin` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleNumerical.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleNumerical.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveCycle`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`):
--
--   ```lean
--   theorem tensor_euler_margin_q68 {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (hd : topologicalKrullDim X ≤ 1) (A : LineBundle X) (hA : A.IsAmple)
--       (L H M N : LineBundle X) (ε : ℝ)
--       (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
--         ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
--           (NumericalAmpleness.curveDegree p L C : ℝ)) :
--       ε * ((eulerCharacteristic p 1 (H.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf : ℤ) : ℝ) ≤
--         ((eulerCharacteristic p 1 (L.tensor N).sheaf - eulerCharacteristic p 1 N.sheaf : ℤ) : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.NumericalAmpleness.IntegralCurve` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.tensor` (definitions bundle `OAIQ068A028` of this split); `OAI.PiExponent.NumericalAmpleness.curveDegree` and `OAI.PiExponentSeshadri.Geometry.eulerCharacteristic` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleNumerical.lean (declaration OAI.PiExponent.CurveCycle.tensor_euler_margin)

import Mathlib
import Definitions.Def_OAIQ068A028
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem tensor_euler_margin_q68 {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (A : LineBundle X) (hA : A.IsAmple)
    (L H M N : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * ((eulerCharacteristic p 1 (H.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf : ℤ) : ℝ) ≤
      ((eulerCharacteristic p 1 (L.tensor N).sheaf - eulerCharacteristic p 1 N.sheaf : ℤ) : ℝ) := by
  sorry

end
end PiExponent.CurveCycle

end OAI
end
