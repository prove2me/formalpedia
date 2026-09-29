-- Prove2me | Theorems.Thm_HopfAlgebra_natCard_algHom_eq_mul_of_surjective
-- name    : HopfAlgebra.natCard_algHom_eq_mul_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/da48f293-1e78-5c0a-9b6f-267ed6608c5f
-- title:
--   Point counts multiply along a surjection of Hopf algebras
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a commutative ring carrying a Hopf $R$-algebra structure and finite as an $R$-module, and let $B$ be a commutative ring carrying a Hopf $R$-algebra structure which is finite and free as an $R$-module. Let $\pi \colon A \to B$ be a morphism of bialgebras over $R$ (notation `→ₐc[R]`) and assume the underlying map is surjective. Let $k$ be an algebraically closed field equipped with an $R$-algebra structure; no assumption is made on its characteristic. Write $\operatorname{hopfKer} \pi$ for the Hopf kernel, i.e. the $R$-subalgebra of $A$ consisting of those $a$ for which the composite of the comultiplication of $A$ with $\mathrm{id}_A \otimes \pi$ agrees on $a$ with the inclusion $a \mapsto a \otimes 1$ of $A$ into $A \otimes_R B$. Then the cardinalities of the sets of $R$-algebra homomorphisms into $k$ satisfy
--   $$\#\operatorname{Hom}_{R\text{-alg}}(A,k) = \#\operatorname{Hom}_{R\text{-alg}}(B,k) \cdot \#\operatorname{Hom}_{R\text{-alg}}(\operatorname{hopfKer}\pi, k),$$
--   the cardinalities being taken as natural numbers (so $0$ for an infinite set).
--
--   In the language of group schemes this is the multiplicativity $\#G(k) = \#(G/H)(k) \cdot \#H(k)$ of $k$-point counts along a surjection $G \to G/H$ of commutative finite group schemes over $R$ with finite locally free quotient, the Hopf kernel being the coordinate ring of $H$. It is the form in which the point-count dévissage is used downstream, for instance in computing the $R$-rank of the Hopf kernel in [`HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective`](thm.html#HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_natCard_algHom_eq_mul_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem HopfAlgebra.natCard_algHom_eq_mul_of_surjective {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) (k : Type x) [Field k] [IsAlgClosed k] [Algebra R k] :
    Nat.card (A →ₐ[R] k) = Nat.card (B →ₐ[R] k) * Nat.card (↥(HopfAlgebra.hopfKer π) →ₐ[R] k) := by sorry
