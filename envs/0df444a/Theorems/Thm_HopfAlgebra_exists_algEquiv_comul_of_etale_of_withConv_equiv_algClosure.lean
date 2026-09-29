-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
-- name    : HopfAlgebra.exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/bbe67a58-f936-5ead-a55b-c225ab8fcde4
-- title:
--   Galois descent: étale Hopf algebras from their Ω-points
-- statement:
--   Let $K$ be a field and $\Omega$ a field extension of $K$ which is algebraically closed, algebraic over $K$ and Galois over $K$, and let $M$ be an additive abelian group equipped with a distributive action of the group $\Omega \simeq_{\mathrm{alg}[K]} \Omega$ of $K$-automorphisms of $\Omega$. Let $A$ be a commutative ring which is a Hopf algebra over $K$ and étale as a $K$-algebra, and let $e_A$ be a bijection from $\mathrm{Hom}_{K\text{-alg}}(A,\Omega)$, regarded via `WithConv` as a monoid under the convolution product coming from the comultiplication of $A$, onto $M$, such that $e_A(f * g) = e_A(f) + e_A(g)$ for all $f, g$, and such that for every $K$-automorphism $\sigma$ of $\Omega$ and all $f, g$ with $g(a) = \sigma(f(a))$ for all $a \in A$ one has $e_A(g) = \sigma \cdot e_A(f)$. Let $B$ with $e_B$ satisfy the same hypotheses, with the same target $M$. Then there exists a $K$-algebra isomorphism $\varphi \colon B \to A$ with $\Delta(\varphi(x)) = (\varphi \otimes \varphi)(\Delta(x))$ for all $x \in B$, where $\Delta$ denotes the comultiplication of the $K$-coalgebra structures. Thus $\varphi$ is an isomorphism of $K$-algebras compatible with comultiplication; compatibility with the counits and antipodes is not asserted.
--
--   This is the Grothendieck–Galois reconstruction statement for étale Hopf algebras over a field: a Galois-equivariant identification of the convolution monoids of $\Omega$-points forces an isomorphism of the underlying algebras respecting comultiplication. It is the general-field input to the results [`HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv`](thm.html#HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv) and [`HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic`](thm.html#HopfAlgebra.exists_algEquiv_comul_of_withConv_equiv_algClosure_padic), and rests on the full faithfulness of the geometric-points functor on étale algebras recorded in [`Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant`](thm.html#Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant), [`Algebra.Etale.algHom_ext_of_forall_comp_eq`](thm.html#Algebra.Etale.algHom_ext_of_forall_comp_eq) and [`Algebra.Etale.eq_of_forall_algHom_apply_eq`](thm.html#Algebra.Etale.eq_of_forall_algHom_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure.lean

import Mathlib
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Bialgebra.Convolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem HopfAlgebra.exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
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
      ∀ x, Coalgebra.comul (R := K) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x) := by sorry
