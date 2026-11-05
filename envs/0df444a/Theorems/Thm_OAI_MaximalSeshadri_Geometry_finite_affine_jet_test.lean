-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_finite_affine_jet_test
-- name    : OAI.MaximalSeshadri.Geometry.finite_affine_jet_test
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:18:29.275803+00:00
-- url     : https://prove2.me/theorems/3c29c302-8786-43a9-a083-6a758e5d6344
-- title:
--   A finite jet test at a point of an étale chart
-- statement:
--   Let $A$ be a $\mathbb C$-algebra with $t_1,t_2\in A$ giving an étale map from $\mathbb C[x_1,x_2]$, $\rho:A\to\mathbb C$ a $\mathbb C$-point, and $n\in\mathbb N$. There is a linear map $J$ from $A$ to functions on the monomials of degree $<n$ in two variables such that $J(a)=0$ if and only if $a\in(\ker\rho)^n$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.finite_affine_jet_test`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/SectionJetDimensions.lean#L29

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.AlgebraicJets MaximalSeshadri.ProjectiveBertini

theorem finite_affine_jet_test {A : Type} [CommRing A] [Algebra ℂ A]
    (t : Fin 2 → A) (het : (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (ρ : A →ₐ[ℂ] ℂ) (n : ℕ) :
    ∃ J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ),
      ∀ a, J a = 0 ↔ a ∈ (RingHom.ker ρ)^n := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
