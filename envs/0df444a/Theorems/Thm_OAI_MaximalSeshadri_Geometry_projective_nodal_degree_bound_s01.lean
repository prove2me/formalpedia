-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_nodal_degree_bound_s01
-- name    : OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:53.438209+00:00
-- url     : https://prove2.me/theorems/127fc7ef-469f-47a3-bff2-071bc915221a
-- title:
--   OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalCurveDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalCurveDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`, `open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets`, `open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal`, `open scoped Topology`):
--
--   ```lean
--   theorem projective_nodal_degree_bound_s01 [IsIntegral X] [IsNoetherian X]
--       {σ : Type} [Fintype σ]
--       (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (hd : topologicalKrullDim X = 1) {M : X.Modules}
--       (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
--       [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
--       (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
--       (i : Y ⟶ X) [IsOpenImmersion i] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
--       (e : L.sheaf.restrict i ≅ O Y)
--       {R : Type} [CommRing R] [Algebra ℂ R] [IsDomain R]
--       (hR : ringKrullDim R ≤ 2)
--       (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
--       (hjets : ∀ n : ℕ,
--         RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--           (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
--             (RingHom.ker (q 0))^n ∧
--         Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
--           (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
--       (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
--       (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
--       (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (hf : f ∉ Ideal.span {g})
--       (π : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
--         R →ₐ[ℂ] Γ(Y,⊤)) (hπ : Function.Surjective π)
--       (hker : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
--         RingHom.ker π.toRingHom = Ideal.span {g})
--       (hcoeff : π f = coefficient e (restrictSection i s)) :
--       (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
--         (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
--           eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O`, `OAI.MaximalSeshadri.Frames.coefficient`, `OAI.MaximalSeshadri.NodalLocal.Bivariate`, `OAI.MaximalSeshadri.NodalLocal.restrictX` and `OAI.MaximalSeshadri.NodalLocal.restrictZ` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor`, `OAI.MaximalSeshadri.AnalyticCoordinates.bivariateTaylor` and `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.baseScalars` and `OAI.MaximalSeshadri.Geometry.eulerCharacteristic` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.nodal_ideal_branch_sum_le_degree_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalCurveDegree.lean (declaration OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

theorem projective_nodal_degree_bound_s01 [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (i : Y ⟶ X) [IsOpenImmersion i] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict i ≅ O Y)
    {R : Type} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hR : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (hf : f ∉ Ideal.span {g})
    (π : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      R →ₐ[ℂ] Γ(Y,⊤)) (hπ : Function.Surjective π)
    (hker : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      RingHom.ker π.toRingHom = Ideal.span {g})
    (hcoeff : π f = coefficient e (restrictSection i s)) :
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
        eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  sorry
end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end
