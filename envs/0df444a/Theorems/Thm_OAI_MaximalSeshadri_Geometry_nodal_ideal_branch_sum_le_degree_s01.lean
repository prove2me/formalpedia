-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_nodal_ideal_branch_sum_le_degree_s01
-- name    : OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:53:59.258313+00:00
-- url     : https://prove2.me/theorems/0cb6a8d9-830f-4c11-97bf-aaa421f153bf
-- title:
--   OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalIdealDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalIdealDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames`, `open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets`, `open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal`, `open scoped Topology`):
--
--   ```lean
--   theorem nodal_ideal_branch_sum_le_degree_s01 (S : Surface)
--       (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
--       (I : S.scheme.IdealSheafData) [IsIntegral I.subscheme]
--       (hd : topologicalKrullDim I.subscheme = 1)
--       (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
--       (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1) (hyI : y ∈ I.support)
--       (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2)
--       (q : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
--         (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
--       (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
--       (hjets : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
--         ∀ n : ℕ,
--         RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--           (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
--             (RingHom.ker (q 0))^n ∧
--         Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--           (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
--       (g : Γ(S.scheme,U.1)) (hg0 : g ≠ 0)
--       (hI : I.ideal U = Ideal.span {g})
--       (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
--       (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
--       (hf : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∉ Ideal.span {g}) :
--       letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
--       let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
--       (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
--         (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
--         curveDegree S L (IntegralCurve.ofIdeal S I hd)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O`, `OAI.MaximalSeshadri.Frames.coefficient`, `OAI.MaximalSeshadri.NodalLocal.Bivariate`, `OAI.MaximalSeshadri.NodalLocal.restrictX` and `OAI.MaximalSeshadri.NodalLocal.restrictZ` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` and `OAI.MaximalSeshadri.Geometry.IntegralCurve.ofIdeal` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor`, `OAI.MaximalSeshadri.AnalyticCoordinates.bivariateTaylor` and `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalIdealDegree.lean (declaration OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES004

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem nodal_ideal_branch_sum_le_degree_s01 (S : Surface)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (I : S.scheme.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme = 1)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
    (U : S.scheme.affineOpens) (y : S.scheme) (hyU : y ∈ U.1) (hyI : y ∈ I.support)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2)
    (q : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(S.scheme,U.1)) (hg0 : g ≠ 0)
    (hI : I.ideal U = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      curveDegree S L (IntegralCurve.ofIdeal S I hd) := by
  sorry

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end
