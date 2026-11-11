-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_smooth_integral_hyperplane_of_etale_atlas_with_equations_s01
-- name    : OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:22.315928+00:00
-- url     : https://prove2.me/theorems/deaf2e62-0356-4a8b-8f39-f554ce6739ca
-- title:
--   OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations_s01 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/BertiniEquations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/BertiniEquations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.BertiniIntegral`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial`, `open MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem smooth_integral_hyperplane_of_etale_atlas_with_equations_s01
--       {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
--       [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
--       (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
--       (hbase : h ≫ projectiveToSpec = g)
--       (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
--       [∀ j, IsDomain Γ(X, (U j).1)]
--       [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
--       (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
--         (U j).2.fromSpec ≫ g)
--       (e : α → (Option (Fin n) ≃ Option (Fin n)))
--       (φ : ∀ j, PolyChart (R := K) (e j none) →+* Γ(X, (U j).1))
--       (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j)) ≫
--         Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X (e j none))
--           (poly_X_mem (e j none)) (by decide) = (U j).2.fromSpec ≫ h)
--       (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
--       [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
--       [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
--       (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j) (hab : ∀ j, a j ≠ b j)
--       (hva : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₁ j)))) =
--         algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
--       (hvb : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₂ j)))) =
--         algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
--       (j₀ : α) (overlap : α → α)
--       (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
--       (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
--       (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
--       ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
--         IsIntegral (projectiveHyperplane h t).subscheme ∧
--         Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
--         ∀ j, (projectiveHyperplane h t).ideal (U j) =
--           Ideal.span {∑ k, φ j (chartConstants (e j none) (t k)) *
--             φ j (chartCoordinate (e j none) k)}
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.BertiniIntegral.projectiveHyperplane`, `OAI.MaximalSeshadri.Projective.PolyChart`, `OAI.MaximalSeshadri.Projective.PolyGrade`, `OAI.MaximalSeshadri.Projective.chartConstants`, `OAI.MaximalSeshadri.Projective.chartCoordinate`, `OAI.MaximalSeshadri.Projective.poly_X_mem` and `OAI.MaximalSeshadri.Projective.projectiveToSpec` (definitions bundle `Q223SES001` of this split).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01` and `OAI.MaximalSeshadri.ProjectiveBertini.exists_smooth_integral_cartier_section_of_local_coordinates_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/BertiniEquations.lean (declaration OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations)

import Mathlib
import Definitions.Def_Q223SES001

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem smooth_integral_hyperplane_of_etale_atlas_with_equations_s01
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hbase : h ≫ projectiveToSpec = g)
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (φ : ∀ j, PolyChart (R := K) (e j none) →+* Γ(X, (U j).1))
    (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j)) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X (e j none))
        (poly_X_mem (e j none)) (by decide) = (U j).2.fromSpec ≫ h)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j) (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₁ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₂ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ j, (projectiveHyperplane h t).ideal (U j) =
        Ideal.span {∑ k, φ j (chartConstants (e j none) (t k)) *
          φ j (chartCoordinate (e j none) k)} := by
  sorry

end
end MaximalSeshadri.BertiniIntegral
end

end
end

end OAI
end
