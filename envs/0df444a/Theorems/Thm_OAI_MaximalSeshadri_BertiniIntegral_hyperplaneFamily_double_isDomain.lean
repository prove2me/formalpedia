-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_hyperplaneFamily_double_isDomain
-- name    : OAI.MaximalSeshadri.BertiniIntegral.hyperplaneFamily_double_isDomain
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:27.579257+00:00
-- url     : https://prove2.me/theorems/f1a675ac-fd14-4493-8abd-45e47fa54446
-- title:
--   Integrality of the double tensor over a generic hyperplane family
-- statement:
--   Let $K$ be a field, $A$ a commutative $K$-algebra with $A\otimes_K A$ a domain, $\sigma$ a finite type, and $v:\sigma\to A$. Suppose $A[\sigma]$ is an algebra over $K[\sigma][X]$, compatibly with $K[\sigma]$, in which $X$ acts as the linear form $\sum_t v_t x_t$. Write $\delta_t=v_t\otimes 1-1\otimes v_t\in A\otimes_K A$. If $i\ne j$ in $\sigma$, $\delta_i\ne 0$, and $\delta_i\mid\delta_j r$ implies $\delta_i\mid r$ for all $r\in A\otimes_K A$, then $A[\sigma]\otimes_{K[\sigma][X]}A[\sigma]$ is a domain.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.BertiniIntegral.hyperplaneFamily_double_isDomain`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Bertini/GenericHyperplanes.lean#L386

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped nonZeroDivisors
open MvPolynomial
variable {R σ : Type*} [CommRing R] [Fintype σ]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R A B σ : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
open Polynomial

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Classical.propDecidable

theorem hyperplaneFamily_double_isDomain {K A σ : Type*} [Field K]
    [CommRing A] [Algebra K A] [Fintype σ] [IsDomain (A ⊗[K] A)]
    [Algebra (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    [IsScalarTower (MvPolynomial σ K) (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A)]
    (v : σ → A)
    (heq : algebraMap (Polynomial (MvPolynomial σ K)) (MvPolynomial σ A) Polynomial.X =
      homogeneousLinearForm v)
    (i j : σ) (hji : j ≠ i)
    (hi : v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i ≠ 0)
    (hij : ∀ r : A ⊗[K] A,
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣
        (v j ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v j) * r →
      (v i ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] v i) ∣ r) :
    IsDomain (MvPolynomial σ A ⊗[Polynomial (MvPolynomial σ K)] MvPolynomial σ A) := by
  sorry

end
end MaximalSeshadri.BertiniIntegral
end
end OAI
