-- Prove2me | Theorems.Thm_OAI_PiExponent_CurveNormalizationMorphism_exists_intrinsic_normalization_morphism_q68
-- name    : OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:41:41.472803+00:00
-- url     : https://prove2.me/theorems/6de2b1f9-7b61-43be-abf7-4c404d998abf
-- title:
--   OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism` of [lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationMorphism.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationMorphism.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.CurveNormalizationMorphism`, with `open AlgebraicGeometry CategoryTheory`, `open CurveNormalizationModel`):
--
--   ```lean
--   theorem exists_intrinsic_normalization_morphism_q68
--       {F : Type u} [Field F] [CharZero F]
--       {X : Scheme.{u}} [IsIntegral X]
--       (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
--       (hdim : topologicalKrullDim X = 1) :
--       letI := structureFieldAlgebra p
--       ∀ (f : X.functionField) (hf : Transcendental F f),
--         ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
--         ∃ g : parameterCurve f hf ⟶ X,
--           g ≫ p = parameterCurveStructureMap f hf ∧
--           parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
--           IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.CurveNormalizationMorphism.structureFieldAlgebra` (definitions bundle `OAIQ068A007` of this split); `OAI.PiExponent.CurveNormalizationModel.parameterCurve` (definitions bundle `OAIQ068A014` of this split); `OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap` (definitions bundle `OAIQ068A022` of this split); `OAI.PiExponent.CurveNormalizationModel.parameterCurveGenericPoint` (definitions bundle `OAIQ068A029` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationMorphism.lean (declaration OAI.PiExponent.CurveNormalizationMorphism.exists_intrinsic_normalization_morphism)

import Mathlib
import Definitions.Def_OAIQ068A007
import Definitions.Def_OAIQ068A029

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveNormalizationMorphism
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel

theorem exists_intrinsic_normalization_morphism_q68
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) :
    letI := structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental F f),
      ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  sorry

end PiExponent.CurveNormalizationMorphism

end

end OAI
end
