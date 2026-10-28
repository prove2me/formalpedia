-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleJetPackets_formalPackets_surjective_of_jetRestriction_q68
-- name    : OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:47:53.381624+00:00
-- url     : https://prove2.me/theorems/1cba2efa-7116-4d00-8009-fa74371a63cf
-- title:
--   OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction` of [lean/OAI/NumberTheory/PiExponent/Jets/AdmissibleJetPackets.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Jets/AdmissibleJetPackets.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.AdmissibleJetPackets`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry`, `open PiExponent.AdmissibleBlowupGeometry`, `open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart`):
--
--   ```lean
--   theorem formalPackets_surjective_of_jetRestriction_q68 (n : ℕ)
--       (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
--       (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
--       Function.Surjective (fun s j =>
--         JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
--           (FormalLogJet.formalJet (d.curveCenters j) (sectionPolynomial d n e s)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.AdmissibleParameters`, `OAI.PiExponent.AdmissibleBlowupGeometry.scale`, `OAI.PiExponent.AdmissibleParameters.curveDegreeWeights`, `OAI.PiExponent.AdmissibleParameters.curveJetWeights`, `OAI.PiExponent.WeightedGeometryScale.Scale` and `OAI.PiExponentSeshadri.Geometry.LineBundle` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponent.CompactLogJetIdeal.coordinateRing` (definitions bundle `OAIQ068A001` of this split); `OAI.PiExponentApprox.FramePolynomial`, `OAI.PiExponent.JetGeometry.RationalCoefficientPacket` and `OAI.PiExponent.JetGeometry.rationalCoefficientPacket` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.affineChart`, `OAI.PiExponent.AdmissibleBlowupGeometry.compactification`, `OAI.PiExponentSeshadri.Geometry.modulePow` and `OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponent.AdmissibleParameters.curveCenters` and `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponent.BlowupJetSurjectivity.jetQuotient` and `OAI.PiExponent.FormalLogJet.formalJet` (definitions bundle `OAIQ068A017` of this split); `OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion`, `OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal` and `OAI.PiExponent.AdmissibleBlowupGeometry.hyperplane` (definitions bundle `OAIQ068A020` of this split); `OAI.PiExponent.BlowupJetSurjectivity.jetRestriction` (definitions bundle `OAIQ068A032` of this split); `OAI.PiExponent.AdmissibleJetPackets.sectionPolynomial`, `OAI.PiExponent.AffineJetCoefficientInterface.Frame` and `OAI.PiExponent.AffineJetCoefficientInterface.Sections` (definitions bundle `OAIQ068A044` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Jets/AdmissibleJetPackets.lean (declaration OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A044

section

attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry
open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart
attribute [local irreducible] AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  AdmissibleBlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem formalPackets_surjective_of_jetRestriction_q68 (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (FormalLogJet.formalJet (d.curveCenters j) (sectionPolynomial d n e s))) := by
  sorry

end PiExponent.AdmissibleJetPackets
end

end OAI
end
