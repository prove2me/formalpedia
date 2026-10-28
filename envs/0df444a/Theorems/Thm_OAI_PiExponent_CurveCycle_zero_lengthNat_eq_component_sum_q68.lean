-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveCycle_zero_lengthNat_eq_component_sum_q68
-- name    : OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:47:15.3896+00:00
-- url     : https://prove2.me/theorems/29315cf0-b566-4717-9262-8f51d676a013
-- title:
--   OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleLengths.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleLengths.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveCycle`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames`, `open PiExponent.SectionZeroIdeal`):
--
--   ```lean
--   theorem zero_lengthNat_eq_component_sum_q68 {X : Scheme.{0}} [IsLocallyNoetherian X]
--       [Fintype (irreducibleComponents X)] (hd : topologicalKrullDim X ≤ 1)
--       (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
--       [Fintype (zeroIdeal L s).subscheme] :
--       letI : ∀ C : irreducibleComponents X,
--         Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
--           (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
--       (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
--         ∑ C : irreducibleComponents X, componentMultiplicity X C *
--           ∑ z, (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
--             (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.Geometry.LineBundle` and `OAI.PiExponentSeshadri.Geometry.structureSheaf` (definitions bundle `OAIQ068A000` of this split); `OAI.PiExponentSeshadri.Geometry.pullbackSection` (definitions bundle `OAIQ068A001` of this split); `OAI.PiExponent.CurveCycle.componentMultiplicity`, `OAI.PiExponent.CurveCycle.reducedComponent`, `OAI.PiExponent.CurveCycle.reducedComponentι` and `OAI.PiExponent.CurveCycle.stalkLength` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponentSeshadri.Geometry.LineBundle.pullback` (definitions bundle `OAIQ068A012` of this split); `OAI.PiExponentSeshadri.Geometry.GlobalSections` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponent.SectionZeroIdeal.zeroIdeal` (definitions bundle `OAIQ068A029` of this split); `OAI.PiExponent.CurveCycle.finite_componentZero` (definitions bundle `OAIQ068A042` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.CurveCycle.tensor_euler_margin_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleLengths.lean (declaration OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum)

import Mathlib
import Definitions.Def_OAIQ068A042

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal

theorem zero_lengthNat_eq_component_sum_q68 {X : Scheme.{0}} [IsLocallyNoetherian X]
    [Fintype (irreducibleComponents X)] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    [Fintype (zeroIdeal L s).subscheme] :
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
      ∑ C : irreducibleComponents X, componentMultiplicity X C *
        ∑ z, (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat := by
  sorry

end
end PiExponent.CurveCycle

end OAI
end
