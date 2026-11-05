-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_QuadraticJets_etale_ordinary_node_realization
-- name    : OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:09:57.799503+00:00
-- url     : https://prove2.me/theorems/0597ec09-a2c5-49c9-9de7-15bf7733eba5
-- title:
--   Analytic realization of an ordinary node on an étale chart
-- statement:
--   Let $A$ be étale over $\mathbb C[x_0,x_1]$, $\rho$ a $\mathbb C$-point killing $x_0,x_1$, $\tau:A\to J$ a map to the algebra of 3-jets in two variables killing $(\ker\rho)^3$ and fixing the coordinates, and $f\in(\ker\rho)^2$ whose 2-jet has nonzero discriminant. Then there is a family $q$ of $\mathbb C$-points of $A$ parametrized by $\mathbb C^2$ with $q_0=\rho$, analytic at 0, with $q_z(f)=u(z)z_1z_2$ near 0 for an analytic $u$ with $u(0)\ne0$, with invertible derivative of $(q_z(x_1),q_z(x_0))$ at 0, and injective on a neighbourhood of 0.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNode.lean#L24

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticNode
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_ordinary_node_realization
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (τ : A →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
      Ideal.Quotient.mk _ (X i))
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) (hdisc : discriminant (τ f) ≠ 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
        (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt
          (fun z => (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
            q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))))
          (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
        ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  sorry

end
end MaximalSeshadri.QuadraticJets
end
end
end
end OAI
