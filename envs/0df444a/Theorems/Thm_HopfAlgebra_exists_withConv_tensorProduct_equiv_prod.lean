-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod
-- name    : HopfAlgebra.exists_withConv_tensorProduct_equiv_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/167046ca-f912-50ba-aece-bc14c5417a70
-- title:
--   Points of a tensor product of Hopf algebras
-- statement:
--   Let $R$ be a commutative ring and $\Gamma$ a group; let $H_1,H_2$ be commutative $R$-algebras carrying Hopf algebra structures over $R$, and let $L$ be a commutative $R$-algebra equipped with an action of $\Gamma$ by ring automorphisms commuting with the $R$-action (so by $R$-algebra automorphisms). The assertion is the existence of a bijection $e$ between $\mathrm{WithConv}$ of the set of $R$-algebra homomorphisms $H_1 \otimes_R H_2 \to L$ — that is, the $L$-valued points of the tensor product, regarded as a monoid under convolution — and the product $\mathrm{WithConv}(H_1 \to_{\mathrm{alg}} L) \times \mathrm{WithConv}(H_2 \to_{\mathrm{alg}} L)$ with componentwise convolution, such that: first, $e(f \cdot g) = e(f) \cdot e(g)$ for all $f,g$, so $e$ is multiplicative for the convolution products; and second, for every $\sigma \in \Gamma$ and all points $f,g$ of $H_1 \otimes_R H_2$ satisfying $g(x) = \sigma \cdot f(x)$ for all $x \in H_1 \otimes_R H_2$, the two components of $e(g)$ and $e(f)$ are related in the same way: $(e(g))_1(y) = \sigma \cdot (e(f))_1(y)$ for all $y \in H_1$, and $(e(g))_2(z) = \sigma \cdot (e(f))_2(z)$ for all $z \in H_2$. The bijection is produced existentially rather than as a bundled monoid isomorphism, and the equivariance is stated in this hypothetical pointwise form.
--
--   This is the functor-of-points statement that a product of affine group schemes represents the product of the point groups, here in Hopf-algebra form and with the $\Gamma$-action on $L$ carried along componentwise. It is used in the construction of flat $\ell$-adic Galois representations, by [`GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index`](thm.html#GaloisRepAdic.isFlatAt_of_forall_point_of_finite_index) and [`GaloisRepAdic.isFlatAt_of_jointly_injective`](thm.html#GaloisRepAdic.isFlatAt_of_jointly_injective), where points of a tensor power of a Hopf algebra are identified with tuples of points of its factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod.lean

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem HopfAlgebra.exists_withConv_tensorProduct_equiv_prod
    {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    (H₁ H₂ : Type) [CommRing H₁] [CommRing H₂] [HopfAlgebra R H₁] [HopfAlgebra R H₂]
    {L : Type} [CommRing L] [Algebra R L] [MulSemiringAction Γ L] [SMulCommClass Γ R L] :
    ∃ e : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) ≃ WithConv (H₁ →ₐ[R] L) × WithConv (H₂ →ₐ[R] L),
      (∀ f g, e (f * g) = e f * e g) ∧
      ∀ (σ : Γ) (f g : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L)),
        (∀ x : H₁ ⊗[R] H₂, g x = σ • (f x)) →
          (∀ y : H₁, (e g).1 y = σ • ((e f).1 y)) ∧ (∀ z : H₂, (e g).2 z = σ • ((e f).2 z)) := by sorry
