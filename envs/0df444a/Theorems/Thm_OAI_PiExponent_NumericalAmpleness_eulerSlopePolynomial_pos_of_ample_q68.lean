-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_pos_of_ample_q68
-- name    : OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:56:48.046705+00:00
-- url     : https://prove2.me/theorems/1904c234-cac0-4a03-b2d5-ba3b86ad41dd
-- title:
--   OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample` of [lean/OAI/NumberTheory/PiExponent/Cohomology/NumericalEulerSlopeInputs.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/NumericalEulerSlopeInputs.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`):
--
--   ```lean
--   theorem eulerSlopePolynomial_pos_of_ample_q68 [IsNoetherian X] [Nonempty X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
--       (hdim : topologicalKrullDim X = d) (a b : ℕ) (hb : 0 < b)
--       (hamp : (slopeBundle L H a b).IsAmple) :
--       0 < (eulerSlopePolynomial p d L H).eval ((a:ℝ)/b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.NumericalAmpleness.slopeBundle` (definitions bundle `OAIQ068A039` of this split); `OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial` (definitions bundle `OAIQ068A046` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/NumericalEulerSlopeInputs.lean (declaration OAI.PiExponent.NumericalAmpleness.eulerSlopePolynomial_pos_of_ample)

import Mathlib
import Definitions.Def_OAIQ068A046

section

attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem eulerSlopePolynomial_pos_of_ample_q68 [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d) (a b : ℕ) (hb : 0 < b)
    (hamp : (slopeBundle L H a b).IsAmple) :
    0 < (eulerSlopePolynomial p d L H).eval ((a:ℝ)/b) := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
