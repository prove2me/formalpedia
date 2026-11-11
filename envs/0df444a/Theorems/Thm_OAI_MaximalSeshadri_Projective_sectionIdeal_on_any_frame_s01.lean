-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_on_any_frame_s01
-- name    : OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:19:05.524627+00:00
-- url     : https://prove2.me/theorems/07385b14-07f6-4186-9a82-6d02daea362c
-- title:
--   OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/PrincipalSectionIdeal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/PrincipalSectionIdeal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback`):
--
--   ```lean
--   lemma sectionIdeal_on_any_frame_s01 {M : X.Modules} (k : K →+* Γ(X, ⊤))
--       (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       (v : σ → K) (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
--       (sectionIdeal k s hs v).ideal U = Ideal.span
--         {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))}
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.Frames.coefficient` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.H0_finite_s01`, `OAI.MaximalSeshadri.Geometry.Surface.H1_finite_s01`, `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.generated_section_H2_untwist_s01`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01`, `OAI.MaximalSeshadri.Projective.exists_global_quartic_smooth_integral_away_s01` and `OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/PrincipalSectionIdeal.lean (declaration OAI.MaximalSeshadri.Projective.sectionIdeal_on_any_frame)

import Mathlib
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma sectionIdeal_on_any_frame_s01 {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) (U : X.affineOpens) (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    (sectionIdeal k s hs v).ideal U = Ideal.span
      {U.1.topIso.hom (coefficient e (restrictSection U.1.ι (sectionCombination k s v)))} := by
  sorry

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end
