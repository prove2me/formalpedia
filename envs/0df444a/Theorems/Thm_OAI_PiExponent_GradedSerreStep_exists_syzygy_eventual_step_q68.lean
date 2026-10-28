-- Prove2me | Theorems.Thm_OAI_PiExponent_GradedSerreStep_exists_syzygy_eventual_step_q68
-- name    : OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:27:20.249918+00:00
-- url     : https://prove2.me/theorems/d68bc1e1-1810-4724-8975-acd4f7111451
-- title:
--   OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step` of [lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSerreStep.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSerreStep.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.GradedSerreStep`, with `open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent`):
--
--   ```lean
--   theorem exists_syzygy_eventual_step_q68 :
--       ∃ (rank : ℕ) (w : Fin rank → ℤ) (g : (Fin rank → MvPolynomial J R) →ₗ[MvPolynomial J R] M),
--         ∃ (hg : ∀ d z, g (DirectSum.decompose (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) z d :
--             Fin rank → MvPolynomial J R) = (DirectSum.decompose 𝓜 (g z) d : M)),
--           Function.Surjective g ∧
--           let hK := GradedSerre.kernel_homogeneous (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) 𝓜 g hg
--           let 𝓚 := HomogeneousSubmoduleGrading.piece (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) g.ker hK
--           ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
--             (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
--             ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.GradedPolynomialLaurent.grading`, `OAI.PiExponent.GradedSerre.kernel_homogeneous`, `OAI.PiExponent.GradedSerre.shiftedFreeGradedSMul`, `OAI.PiExponent.HomogeneousSubmoduleGrading.gradedSMul`, `OAI.PiExponent.HomogeneousSubmoduleGrading.piece`, `OAI.PiExponent.ShiftedFreeGrading.decomposition` and `OAI.PiExponent.ShiftedFreeGrading.piece` (definitions bundle `OAIQ068A008` of this split); `OAI.PiExponent.GradedSerreStep.HasPrimitive` and `OAI.PiExponent.GradedSerreStep.HasRecovery` (definitions bundle `OAIQ068A025` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.ReesSheafCechRecovery.eventually_recovery_and_cohomology_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSerreStep.lean (declaration OAI.PiExponent.GradedSerreStep.exists_syzygy_eventual_step)

import Mathlib
import Definitions.Def_OAIQ068A025

section

attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GradedSerreStep
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R M σM : Type*} [Fintype J] [DecidableEq J] [CommRing R]
  [IsNoetherianRing R] [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

omit [IsNoetherianRing R] in
theorem exists_syzygy_eventual_step_q68 :
    ∃ (rank : ℕ) (w : Fin rank → ℤ) (g : (Fin rank → MvPolynomial J R) →ₗ[MvPolynomial J R] M),
      ∃ (hg : ∀ d z, g (DirectSum.decompose (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) z d :
          Fin rank → MvPolynomial J R) = (DirectSum.decompose 𝓜 (g z) d : M)),
        Function.Surjective g ∧
        let hK := GradedSerre.kernel_homogeneous (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) 𝓜 g hg
        let 𝓚 := HomogeneousSubmoduleGrading.piece (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) g.ker hK
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
          ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  sorry

end
end PiExponent.GradedSerreStep

end OAI
end
