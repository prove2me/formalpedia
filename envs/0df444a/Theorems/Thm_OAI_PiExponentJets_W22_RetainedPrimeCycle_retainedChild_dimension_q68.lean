-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_RetainedPrimeCycle_retainedChild_dimension_q68
-- name    : OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:30:16.082866+00:00
-- url     : https://prove2.me/theorems/81794f0b-8500-43cd-a165-32e6463fa803
-- title:
--   OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22.RetainedPrimeCycle`):
--
--   ```lean
--   theorem retainedChild_dimension_q68
--       (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
--       (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
--       (hparent : ∀ a,
--         (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
--       (T : Ideal (MvPolynomial σ k)) (a : C.Index)
--       (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
--       ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentJets.W22.RetainedMinimalPrime` and `OAI.PiExponentJets.W22.ProjectiveComponent.homogeneous` (definitions bundle `OAIQ068A009` of this split); `OAI.PiExponentJets.W22.RetainedPrimeCycle` (definitions bundle `OAIQ068A018` of this split); `OAI.PiExponentJets.W22.actualHP` (definitions bundle `OAIQ068A027` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68` and `OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean (declaration OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A027

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22.RetainedPrimeCycle

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem retainedChild_dimension_q68
    (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
    (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
    (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (a : C.Index)
    (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
    ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ) := by
  sorry

end PiExponentJets.W22.RetainedPrimeCycle

end OAI
end
