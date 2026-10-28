-- Prove2me | Theorems.Thm_OAI_PiExponent_ReesSheafCechRecovery_eventually_recovery_and_cohomology_q68
-- name    : OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:58:50.254356+00:00
-- url     : https://prove2.me/theorems/0692c218-991f-4c53-a4e1-76180fbf2739
-- title:
--   OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology` of [lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechRecovery.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechRecovery.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.ReesSheafCechRecovery`, with `open CategoryTheory AlgebraicGeometry TopologicalSpace`, `open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque`, `open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality`, `open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation`, `open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech`):
--
--   ```lean
--   theorem eventually_recovery_and_cohomology_q68
--       (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
--       ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
--         Function.Bijective (ordinaryGlobalSection I a ha n) ∧
--         ∀ (q : ℕ) (x : CategoryTheory.Abelian.Ext.{1} (C := (affineBlowup I).Modules)
--           (schemeFreeOpen (affineBlowup I) ⊤) (exceptionalPower I n) (q+1)), x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentSeshadri.ReesGrading.affineBlowup` (definitions bundle `OAIQ068A001` of this split); `OAI.PiExponentSeshadri.Geometry.schemeHasExt` (definitions bundle `OAIQ068A003` of this split); `OAI.PiExponent.ReesSheafCechRecovery.schemeFreeOpen` (definitions bundle `OAIQ068A042` of this split); `OAI.PiExponent.ReesSheafCechBase.exceptionalPower` (definitions bundle `OAIQ068A044` of this split); `OAI.PiExponent.ReesSheafCechRecovery.ordinaryGlobalSection` (definitions bundle `OAIQ068A046` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechRecovery.lean (declaration OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology)

import Mathlib
import Definitions.Def_OAIQ068A046

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

variable [IsNoetherianRing R]

theorem eventually_recovery_and_cohomology_q68
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ (q : ℕ) (x : CategoryTheory.Abelian.Ext.{1} (C := (affineBlowup I).Modules)
        (schemeFreeOpen (affineBlowup I) ⊤) (exceptionalPower I n) (q+1)), x = 0 := by
  sorry

end
end PiExponent.ReesSheafCechRecovery

end OAI
end
