-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_actualHP_natDegree_of_prime_dimension_q68
-- name    : OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:31:17.861598+00:00
-- url     : https://prove2.me/theorems/e216706d-ffb0-4df4-b73b-c24a8b02af81
-- title:
--   OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeCutBudget.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeCutBudget.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22`, with `open PiExponentJets.W64`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem actualHP_natDegree_of_prime_dimension_q68
--       (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
--       (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
--       (v : σ) (hv : MvPolynomial.X v ∉ Q) (s : ℕ)
--       (hdim : ringKrullDim (MvPolynomial σ k ⧸ Q) = (s+1 : ℕ)) :
--       (actualHP Q hQ).natDegree = s
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentJets.W22.actualHP` (definitions bundle `OAIQ068A027` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68` and `OAI.PiExponentJets.W22.homogeneous_prefix_hilbert_degree_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeCutBudget.lean (declaration OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A027

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem actualHP_natDegree_of_prime_dimension_q68
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ Q) (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ Q) = (s+1 : ℕ)) :
    (actualHP Q hQ).natDegree = s := by
  sorry

end PiExponentJets.W22

end OAI
end
