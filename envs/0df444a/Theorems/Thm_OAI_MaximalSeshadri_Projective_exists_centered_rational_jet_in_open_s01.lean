-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Projective_exists_centered_rational_jet_in_open_s01
-- name    : OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:08:15.044032+00:00
-- url     : https://prove2.me/theorems/bc087b67-6ba6-4c97-9a71-c91f7c8d59e9
-- title:
--   OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/FramedNodalChart.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/FramedNodalChart.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Projective`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial`, `open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini`, `open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets`):
--
--   ```lean
--   theorem exists_centered_rational_jet_in_open_s01 [IsIntegral X]
--       (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
--       (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
--       (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
--       [IsClosedImmersion (sectionsMorphism k s hs)]
--       (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
--       (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
--       ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
--         ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
--           let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
--           ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
--             ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
--               (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
--               RingHom.ker τ = (RingHom.ker ρ)^3 ∧
--               (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
--               (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
--                 -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
--               (MvPolynomial.eval₂Hom (openScalars g U.1)
--                 (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
--               ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.AlgebraicJets.JetAlgebra`, `OAI.MaximalSeshadri.Frames.O` and `OAI.MaximalSeshadri.Projective.projectiveToSpec` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` and `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.AlgebraicJets.jetAugment` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Projective.affineSectionRatios` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.centeredOpen` and `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/FramedNodalChart.lean (declaration OAI.MaximalSeshadri.Projective.exists_centered_rational_jet_in_open)

import Mathlib
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme} {M : X.Modules}

theorem exists_centered_rational_jet_in_open_s01 [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
        ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
          ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
            (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
            RingHom.ker τ = (RingHom.ker ρ)^3 ∧
            (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
            (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
              -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
            (MvPolynomial.eval₂Hom (openScalars g U.1)
              (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
            ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  sorry

end
end MaximalSeshadri.Projective

end

end OAI
end
