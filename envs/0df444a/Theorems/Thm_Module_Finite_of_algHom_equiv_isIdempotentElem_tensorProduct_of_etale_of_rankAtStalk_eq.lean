-- Prove2me | Theorems.Thm_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
-- name    : Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/c3d0f97e-badb-5a4a-8f5a-eac9996773ed
-- title:
--   Finiteness of an algebra representing idempotents of Q
-- statement:
--   Let $R$ be a commutative ring and $Q$ a commutative $R$-algebra which is finite as an $R$-module and étale over $R$, and let $r$ be a natural number such that the rank of $Q$ at the stalk of every point $p$ of the prime spectrum of $R$ equals $r$ (so $Q$ is of constant rank $r$). Let $C$ be a further commutative $R$-algebra, and suppose given, for every commutative $R$-algebra $S$ (in the same universe as $R$, $Q$, $C$), a bijection $\eta_S$ from the set of $R$-algebra homomorphisms $C \to S$ onto the set of idempotent elements $e$ of $S \otimes_R Q$, i.e. those with $e \cdot e = e$. Suppose further that this family is natural in $S$: for all commutative $R$-algebras $S$, $T$, every $R$-algebra homomorphism $g \colon S \to T$ and every $R$-algebra homomorphism $c \colon C \to S$, the idempotent $\eta_T(g \circ c)$ equals the image of $\eta_S(c)$ under $g \otimes \mathrm{id}_Q \colon S \otimes_R Q \to T \otimes_R Q$. Then $C$ is a finite (that is, finitely generated) $R$-module.
--
--   In geometric terms: if a scheme represents the functor of open-and-closed subschemes of a finite étale $R$-scheme of constant rank, then it is finite over $R$. Together with the construction of such a representing algebra it yields that the open-and-closed subschemes of a finite étale scheme of constant rank are represented by a finite étale scheme; it is cited by [`AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale`](thm.html#AlgebraicGeometry.exists_isFinite_etale_represents_clopens_of_isFinite_of_etale), the finiteness input for relative representability of level structures by finite étale schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Algebra.Etale R Q]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) Q p = r)
    (C : Type u) [CommRing C] [Algebra R C]
    (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e})
    (hη : ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q)) :
    Module.Finite R C := by sorry
