-- Prove2me | Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedTop_power_cartier_restriction_q68
-- name    : OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:53:58.026063+00:00
-- url     : https://prove2.me/theorems/ae71b3f0-10a9-4a96-a8e8-c9a10df6dc1f
-- title:
--   OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction` of [lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerRestriction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerRestriction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.NumericalAmpleness`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`, `open PiExponent.SectionZeroIdeal`):
--
--   ```lean
--   theorem mixedTop_power_cartier_restriction_q68 [IsNoetherian X]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
--       (hdim : topologicalKrullDim X ≤ d+1)
--       (A : LineBundle X) (n : ℕ) (s : GlobalSections X (A.pow n).sheaf) [Mono s]
--       (ls : List (LineBundle X)) (hlen : ls.length = d) :
--       (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) =
--         mixedTop (lineEuler ((zeroIdeal (A.pow n) s).subschemeι ≫ p) d)
--           (ls.map (fun L => L.pullback (zeroIdeal (A.pow n) s).subschemeι))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pow` and `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.IsAmple` (definitions bundle `OAIQ068A021` of this split); `OAI.PiExponent.SectionZeroIdeal.zeroIdeal` (definitions bundle `OAIQ068A029` of this split); `OAI.PiExponent.NumericalAmpleness.mixedTop` (definitions bundle `OAIQ068A042` of this split); `OAI.PiExponent.NumericalAmpleness.lineEuler` (definitions bundle `OAIQ068A043` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerRestriction.lean (declaration OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction)

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
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem mixedTop_power_cartier_restriction_q68 [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (n : ℕ) (s : GlobalSections X (A.pow n).sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal (A.pow n) s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal (A.pow n) s).subschemeι)) := by
  sorry

end
end PiExponent.NumericalAmpleness

end OAI
end
