-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_generic_hyperplane_section_over_model
-- name    : OAI.MaximalSeshadri.BertiniIntegral.generic_hyperplane_section_over_model
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:38.183442+00:00
-- url     : https://prove2.me/theorems/8c7e5077-49a1-485e-80fc-21958a1267bd
-- title:
--   A generic hyperplane section over a countable model is a domain
-- statement:
--   Let $R\subset K$ be fields of characteristic zero (with $K$ an $R$-algebra), $A$ a domain over $K$ with $A\otimes_K A$ a domain, and $A_0$ an $R$-algebra with an isomorphism $e:K\otimes_R A_0\cong A$ of $K$-algebras. Let $\sigma$ be finite, $v_0:\sigma\to A_0$, $v:\sigma\to A$ with $e(1\otimes v_{0,i})=v_i$, and suppose $\operatorname{aeval}$ of the linear form $\sum v_kx_k$ is injective on $K[\sigma][X]$. If $i\neq j$, $v_j$ is transcendental over $K$ (Mathlib's predicate `Transcendental K`), $\delta_i\ne0$ and $\delta_i\mid\delta_jr$ implies $\delta_i\mid r$ in $A\otimes_KA$, where $\delta_t=v_t\otimes1-1\otimes v_t$, then for each injective $R$-algebra map $f:R[\sigma][X]\to K$ the quotient of $A$ by the element $f(X)-\sum_k f(x_k)v_k$ is a domain.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.BertiniIntegral.generic_hyperplane_section_over_model`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Bertini/SimultaneousHyperplanes.lean#L18

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem generic_hyperplane_section_over_model {R K A A₀ σ : Type}
    [Field R] [CharZero R] [Field K] [CharZero K]
    [Algebra R K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra R A]
    [IsScalarTower R K A] [IsDomain (A ⊗[K] A)]
    [CommRing A₀] [Algebra R A₀] [Fintype σ]
    (e : (K ⊗[R] A₀) ≃ₐ[K] A) (v₀ : σ → A₀) (v : σ → A)
    (hv : ∀ i, e (1 ⊗ₜ[R] v₀ i) = v i)
    (hdom : Function.Injective (Polynomial.aeval (homogeneousLinearForm v) :
      (MvPolynomial σ K)[X] →ₐ[MvPolynomial σ K] MvPolynomial σ A))
    (i j : σ) (hji : j ≠ i) (hj : Transcendental K (v j))
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    ∀ f : (MvPolynomial σ R)[X] →ₐ[R] K, Function.Injective f →
      IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
        ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  sorry

end
end MaximalSeshadri.BertiniIntegral
end
end
end OAI
