-- Prove2me | Theorems.Thm_OAI_PiExponent_AffineReesCanonicalRecovery_eventually_comap_bijective_q68
-- name    : OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:52:07.668158+00:00
-- url     : https://prove2.me/theorems/64b44433-8fa2-4329-b99d-93cd4d0afd5c
-- title:
--   OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective` of [lean/OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.AffineReesCanonicalRecovery`, with `open AlgebraicGeometry CategoryTheory`, `open PiExponentSeshadri.Geometry PiExponentSeshadri.ReesGrading PiExponentSeshadri.IdealPullback`, `open CanonicalRecoveryProperties`):
--
--   ```lean
--   theorem eventually_comap_bijective_q68 {R : Type} [CommRing R] [IsNoetherianRing R]
--       (I : Ideal R) :
--       ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
--         ComapBijective (projection I) (specIdeal (I^n)) ⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.IdealPullback.specIdeal`, `OAI.PiExponentSeshadri.ReesGrading.affineBlowup` and `OAI.PiExponentSeshadri.ReesGrading.projection` (definitions bundle `OAIQ068A001` of this split); `OAI.PiExponentSeshadri.ReesGrading.projection_proper` (definitions bundle `OAIQ068A013` of this split); `OAI.PiExponent.CanonicalRecoveryProperties.ComapBijective` (definitions bundle `OAIQ068A044` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.main` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean (declaration OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective)

import Mathlib
import Definitions.Def_OAIQ068A044

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineReesCanonicalRecovery
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.ReesGrading PiExponentSeshadri.IdealPullback
open CanonicalRecoveryProperties
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion

theorem eventually_comap_bijective_q68 {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ComapBijective (projection I) (specIdeal (I^n)) ⊤ := by
  sorry

end PiExponent.AffineReesCanonicalRecovery

end

end OAI
end
