-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_smooth_integral_zero_family_with_equations
-- name    : OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_zero_family_with_equations
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:28.760194+00:00
-- url     : https://prove2.me/theorems/8c6458e9-e713-4e77-9baa-9dcb2c2ea137
-- title:
--   A Bertini family with local equations
-- statement:
--   Let $K$ be an uncountable algebraically closed field of characteristic zero, $X$ a scheme over $K$ with a countable family of affine opens $U_j$ covering it, each with domain sections, finite type over $K$ and étale over a polynomial ring in variables $\sigma_j$, and functions $v_j$ on $U_j$ two of which are distinct coordinates. Let $D(t)$ be opens with $D(t)\cap U_j$ the basic open of $t(e_j\mathrm{none})-\sum_kt(e_j(k))v_{j,k}$, and suppose the $U_j$ overlap a common $U_{j_0}$. For every nonzero polynomial $q$ there is $t$ with $q(t)\neq0$ such that the complement of $D(t)$ with its vanishing ideal is integral, smooth over $K$, and locally generated on each $U_j$ by the displayed element.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_zero_family_with_equations`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/BertiniEquations.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

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

theorem smooth_integral_zero_family_with_equations
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (v : ∀ j, Fin n → Γ(X, (U j).1)) (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (D : (Option (Fin n) → K) → X.Opens)
    (hD : ∀ t j, (U j).2.fromSpec ⁻¹ᵁ D t = PrimeSpectrum.basicOpen
      (algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal (D t).compl).subscheme ∧
      Smooth ((Scheme.IdealSheafData.vanishingIdeal (D t).compl).subschemeι ≫ g) ∧
      ∀ j, (Scheme.IdealSheafData.vanishingIdeal (D t).compl).ideal (U j) =
        Ideal.span {algebraMap K Γ(X, (U j).1) (t (e j none)) -
          ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
  sorry

end
end MaximalSeshadri.BertiniIntegral
end
end
end
end OAI
