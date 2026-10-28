-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample_q68
-- name    : OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:52:48.391811+00:00
-- url     : https://prove2.me/theorems/8847a328-6131-45c0-81f5-c5e31955cb64
-- title:
--   OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample` of [lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAmpleDimension.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAmpleDimension.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective`, `open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1`):
--
--   ```lean
--   theorem mixedDifference_lineEuler_of_ample_q68 {X : Scheme.{0}} [IsNoetherian X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
--       (hdim : topologicalKrullDim X ≤ d)
--       (ls : List (LineBundle X)) (hlen : ls.length = d+1) :
--       mixedDifference ls (lineEuler p d) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.NumericalAmpleness.mixedDifference` (definitions bundle `OAIQ068A042` of this split); `OAI.PiExponent.NumericalAmpleness.lineEuler` (definitions bundle `OAIQ068A043` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_eval_nat_div_q68`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_derivative_margin_q68`, `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68`, `OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68`, `OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68` and `OAI.PiExponent.NumericalAmpleness.topEuler_slopeBundle_eq_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAmpleDimension.lean (declaration OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample)

import Mathlib
import Definitions.Def_OAIQ068A043

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

theorem mixedDifference_lineEuler_of_ample_q68 {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (ls : List (LineBundle X)) (hlen : ls.length = d+1) :
    mixedDifference ls (lineEuler p d) = 0 := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
