-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample_q68
-- name    : OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:42:57.587964+00:00
-- url     : https://prove2.me/theorems/e54255c5-abc2-4b0f-b98a-54b995983f99
-- title:
--   OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample` of [lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCurveDegreePositive.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCurveDegreePositive.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry`):
--
--   ```lean
--   theorem curveDegree_pos_of_ample_q68
--       {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (L : LineBundle X) (hL : L.IsAmple) (C : IntegralCurve X) :
--       0 < curveDegree p L C
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.NumericalAmpleness.IntegralCurve` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.NumericalAmpleness.curveDegree` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68`, `OAI.PiExponent.BlowupCurveMargin.margin_of_image_outside_chart_q68`, `OAI.PiExponent.NumericalAmpleness.ample_slope_of_polynomial_pos_of_lower_criterion_q68` and `OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCurveDegreePositive.lean (declaration OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample)

import Mathlib
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.NumericalAmpleness
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

theorem curveDegree_pos_of_ample_q68
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (C : IntegralCurve X) :
    0 < curveDegree p L C := by
  sorry

end PiExponent.NumericalAmpleness

end

end OAI
end
