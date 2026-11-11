-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_AnalyticCoordinates_analyticTaylor_exactJets_s01
-- name    : OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:36.01362+00:00
-- url     : https://prove2.me/theorems/52228f8b-8433-4cf1-9850-2463baeab6b2
-- title:
--   OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets` of [lean/OAI/AlgebraicGeometry/Seshadri/Jets/AnalyticFullRank.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/AnalyticFullRank.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.AnalyticCoordinates`, with `open scoped Topology`, `open AlgebraicJets FormalCoordinates MvPolynomial`):
--
--   ```lean
--   theorem analyticTaylor_exactJets_s01
--       [Algebra (MvPolynomial (Fin 2) ℂ) S]
--       [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
--       [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
--       [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]
--       (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
--       (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
--       (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
--       (he : HasFDerivAt (fun z =>
--         (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
--          q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))))
--          (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) (n : ℕ) :
--       RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--         (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
--           (RingHom.ker (q 0))^n ∧
--       Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--         (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor` (definitions bundle `Q223SES004` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/AnalyticFullRank.lean (declaration OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets)

import Mathlib
import Definitions.Def_Q223SES004

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology

open AlgebraicJets FormalCoordinates MvPolynomial
variable {S : Type*} [CommRing S] [Algebra ℂ S]

theorem analyticTaylor_exactJets_s01
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))))
       (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) := by
  sorry

end
end MaximalSeshadri.AnalyticCoordinates

end

end
end

end OAI
end
