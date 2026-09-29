-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
-- name    : HopfAlgebra.exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/9a7ca5a5-5986-53e9-b7cd-5494b757047d
-- title:
--   Étale Hopf algebras with matching Galois modules of Ω-points
-- statement:
--   Let $K$ be a field and $\Omega$ a field equipped with a $K$-algebra structure which is algebraically closed, algebraic over $K$ and Galois over $K$, and let $M$ be an additive commutative group carrying a distributive multiplicative action of the Galois group $\Omega \simeq_{\mathrm{alg}[K]} \Omega$. Let $A$ be a commutative ring which is both a Hopf algebra over $K$ and an étale $K$-algebra, and let $e_A$ be a bijection from `WithConv (A →ₐ[K] Ω)`, the set of $K$-algebra homomorphisms $A \to \Omega$ with its convolution multiplication, onto $M$, such that $e_A(f \cdot g) = e_A f + e_A g$ for all $f,g$, and such that for every $K$-automorphism $\sigma$ of $\Omega$ and all $f,g$ with $g(a) = \sigma(f(a))$ for all $a \in A$ one has $e_A g = \sigma \bullet e_A f$. Let $B$, $e_B$ satisfy the same hypotheses. Then there exists a $K$-algebra isomorphism $\varphi : B \to A$ such that $\mathrm{comul}(\varphi x) = (\varphi \otimes \varphi)(\mathrm{comul}\, x)$ and $\mathrm{counit}(\varphi x) = \mathrm{counit}(x)$ for all $x \in B$, and such that for every $f : A \to \Omega$ in `WithConv (A →ₐ[K] Ω)` the composite of $\varphi$ with $f$ satisfies $e_B(f \circ \varphi) = e_A f$. Compatibility of $\varphi$ with the antipodes is not asserted.
--
--   This is the rigidity half of the anti-equivalence between finite étale commutative group schemes over $K$ and discrete Galois modules: two étale commutative Hopf algebras whose groups of $\Omega$-points are identified, compatibly with the group law and the Galois action, with one and the same module $M$ are isomorphic as Hopf algebras by an isomorphism inducing the given identification. It is used in the construction of a finite flat model with prescribed torsion and Hecke action on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure.lean

import Mathlib
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Bialgebra.Convolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_algEquiv_comul_counit_withConv_comp_of_etale_of_withConv_equiv_algClosure
    (K : Type*) [Field K] (Ω : Type*) [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Ω ≃ₐ[K] Ω) M]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.Etale K A]
    (eA : WithConv (A →ₐ[K] Ω) ≃ M)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (A →ₐ[K] Ω)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (B : Type*) [CommRing B] [HopfAlgebra K B] [Algebra.Etale K B]
    (eB : WithConv (B →ₐ[K] Ω) ≃ M)
    (heB_add : ∀ f g, eB (f * g) = eB f + eB g)
    (heB_act : ∀ (σ : Ω ≃ₐ[K] Ω) (f g : WithConv (B →ₐ[K] Ω)),
      (∀ b : B, g b = σ (f b)) → eB g = σ • (eB f)) :
    ∃ φ : B ≃ₐ[K] A,
      (∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) ∧
      (∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x) ∧
      ∀ f : WithConv (A →ₐ[K] Ω),
        eB (WithConv.toConv ((WithConv.ofConv f).comp φ.toAlgHom)) = eA f := by sorry
