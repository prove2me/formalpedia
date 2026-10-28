-- Prove2me | Theorems.Thm_OAI_PiExponent_BlowupCurveMargin_margin_of_nonnegative_degree_q68
-- name    : OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:39:41.881954+00:00
-- url     : https://prove2.me/theorems/dd2e9f21-77be-4758-a18f-fc666d74e236
-- title:
--   OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree` of [lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupCurveMargin.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupCurveMargin.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.BlowupCurveMargin`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry`, `open NumericalAmpleness`):
--
--   ```lean
--   theorem margin_of_nonnegative_degree_q68
--       (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
--       (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
--       (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
--       (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
--       marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
--         (curveDegree p (A.tensor J) C : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.BlowupCurveMargin.marginCoefficient` and `OAI.PiExponent.NumericalAmpleness.IntegralCurve` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pow` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.tensor` (definitions bundle `OAIQ068A028` of this split); `OAI.PiExponent.NumericalAmpleness.curveDegree` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68`, `OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68` and `OAI.PiExponent.BlowupCurveMargin.margin_of_image_outside_chart_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupCurveMargin.lean (declaration OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A028
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

theorem margin_of_nonnegative_degree_q68
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  sorry

end PiExponent.BlowupCurveMargin

end

end OAI
end
