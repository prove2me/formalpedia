-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
-- name    : HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/cc15c2fd-ca52-5dcc-9f3f-b4cb096a4619
-- title:
--   Uniqueness of finite Hopf algebras over ℚₚ with given Galois module of points
-- statement:
--   Let $p$ be a prime, and let $M$ be an additive abelian group equipped with a distributive multiplicative action of the group $\operatorname{Aut}_{\mathbb{Q}_p}(\overline{\mathbb{Q}_p}) = (\overline{\mathbb{Q}_p} \simeq_{\mathrm{alg}[\mathbb{Q}_p]} \overline{\mathbb{Q}_p})$, where $\overline{\mathbb{Q}_p}$ is `AlgebraicClosure ℚ_[p]`. Let $A$ be a commutative ring with a Hopf algebra structure over $\mathbb{Q}_p$ which is finite as a $\mathbb{Q}_p$-module and whose comultiplication is cocommutative, and suppose given a bijection $e_A$ from `WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])`, the type of $\mathbb{Q}_p$-algebra homomorphisms $A \to \overline{\mathbb{Q}_p}$ carried by the type synonym on which the convolution product is written multiplicatively, onto $M$, such that $e_A(f \cdot g) = e_A f + e_A g$ for all $f, g$, and such that whenever $\sigma$ is a $\mathbb{Q}_p$-automorphism of $\overline{\mathbb{Q}_p}$ and $g$ satisfies $g(a) = \sigma(f(a))$ for all $a \in A$, one has $e_A g = \sigma \bullet e_A f$. Let $B$ with $e_B$ satisfy the same hypotheses. Then there is a $\mathbb{Q}_p$-algebra isomorphism $\varphi : B \simeq A$ which is a morphism of coalgebras, i.e. $\Delta(\varphi x) = (\varphi \otimes \varphi)(\Delta x)$ for all $x \in B$.
--
--   This is the uniqueness half of the Grothendieck–Galois dictionary for finite commutative group schemes over a $p$-adic field: a finite Hopf algebra over $\mathbb{Q}_p$ is determined, as an algebra with comultiplication, by the Galois module of its $\overline{\mathbb{Q}_p}$-points. It is used in the construction of finite free Hopf orders over $\mathbb{Z}_p$ of rank $p^2$ attached to a Weierstrass curve with unit discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_comul_of_withConv_equiv_algClosure_padic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic
    (p : ℕ) [Fact p.Prime]
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (A : Type) [CommRing A] [HopfAlgebra ℚ_[p] A]
    (hAfin : Module.Finite ℚ_[p] A) (hAcocomm : Coalgebra.IsCocomm ℚ_[p] A)
    (eA : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type) [CommRing B] [HopfAlgebra ℚ_[p] B]
    (hBfin : Module.Finite ℚ_[p] B) (hBcocomm : Coalgebra.IsCocomm ℚ_[p] B)
    (eB : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (B →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[ℚ_[p]] A,
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by sorry
