-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic
-- name    : HopfAlgebra.exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3f318b6b-bb6e-53de-abee-c6da099b47ba
-- title:
--   Transporting ℚ̄ₚ-points along a base-change bialgebra isomorphism
-- statement:
--   Fix a prime $p$ and let $M$ be an additive abelian group carrying a distributive multiplicative action of the group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ of $\mathbb{Q}_p$-algebra automorphisms of `AlgebraicClosure ℚ_[p]`. Let $A$ be a commutative ring equipped with a Hopf algebra structure over $\mathbb{Q}_p$, and let $e_A$ be a bijection from `WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])`, the set of $\mathbb{Q}_p$-algebra homomorphisms $A \to \overline{\mathbb{Q}}_p$ with its convolution multiplication $f * g = m \circ (f \otimes g) \circ \Delta$, onto $M$, such that (i) $e_A(f*g) = e_A f + e_A g$ for all $f, g$, and (ii) whenever $\sigma$ is a $\mathbb{Q}_p$-automorphism of $\overline{\mathbb{Q}}_p$ and $g(a) = \sigma(f(a))$ for every $a \in A$, one has $e_A g = \sigma \cdot e_A f$. Let $H$ be a commutative ring with a Hopf algebra structure over $\mathbb{Z}_p$, and let $\varphi : \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H \to A$ be an isomorphism of $\mathbb{Q}_p$-algebras satisfying $\Delta_A(\varphi x) = (\varphi \otimes \varphi)(\Delta_{\mathbb{Q}_p \otimes H} x)$ for all $x$ (compatibility with comultiplication only; no condition on counit or antipode is imposed). Then there exists a bijection $e$ from `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])` onto $M$ with the same two properties: $e(f*g) = e f + e g$, and $e g = \sigma \cdot e f$ whenever $g(h) = \sigma(f(h))$ for all $h \in H$.
--
--   This transports a Galois-equivariant identification of the $\overline{\mathbb{Q}}_p$-points of a $\mathbb{Q}_p$-Hopf algebra with an abstract Galois module $M$ across a base-change isomorphism $\mathbb{Q}_p \otimes_{\mathbb{Z}_p} H \cong A$, so that the points of the integral model $H$ acquire the same description. It is used in the construction of finite flat prolongations of the torsion of a Weierstrass curve over $\mathbb{Z}_p$ with unit discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_withConv_equiv_padicInt_of_algEquiv_baseChange_padic
    (p : ℕ) [Fact p.Prime]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (φ : (ℚ_[p] ⊗[ℤ_[p]] H) ≃ₐ[ℚ_[p]] A)
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x)) :
    ∃ e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
