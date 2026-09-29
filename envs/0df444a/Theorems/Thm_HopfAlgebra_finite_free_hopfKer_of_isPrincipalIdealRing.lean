-- Prove2me | Theorems.Thm_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing
-- name    : HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b774f8e7-bd75-5396-9e17-e24ceb537bcd
-- title:
--   Hopf kernel is finite free over a PID
-- statement:
--   Let $R$ be a principal ideal domain (a commutative ring that is a domain and in which every ideal is principal), let $A$ be a commutative $R$-bialgebra which is finitely generated and free as an $R$-module, let $B$ be a commutative $R$-bialgebra, and let $\pi \colon A \to B$ be a morphism of $R$-bialgebras. The Hopf kernel [`HopfAlgebra.hopfKer π`](def/HopfAlgebra_HopfKer.html#L19) is the $R$-subalgebra of $A$ defined as the equaliser of two $R$-algebra maps $A \to A \otimes_R B$: the coaction $(\mathrm{id}_A \otimes \pi) \circ \Delta_A$, and the inclusion $a \mapsto a \otimes 1$; that is, it consists of those $a \in A$ with $(\mathrm{id}_A \otimes \pi)(\Delta a) = a \otimes 1$. The conclusion is the conjunction of two statements about this subalgebra viewed as an $R$-module: it is finitely generated, and it is free. No hypothesis is imposed on $B$ or on $\pi$ beyond their being a commutative $R$-bialgebra and a bialgebra map, and no Hopf-algebra structure on $A$ is assumed.
--
--   This is the elementary module-theoretic input for the Hopf-kernel construction $A^{\mathrm{co}\pi}$: over a principal ideal domain, the ring of coinvariants of a bialgebra quotient map inherits finiteness and freeness (hence flatness) from $A$. It is used in the comparison of ranks [`HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective`](thm.html#HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective) and in the construction of a connected–étale sequence over $\mathbb{Z}_p$, [`HopfAlgebra.exists_connected_etale_sequence_padicInt`](thm.html#HopfAlgebra.exists_connected_etale_sequence_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.finite_free_hopfKer_of_isPrincipalIdealRing {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) :
    Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Free R ↥(HopfAlgebra.hopfKer π) := by sorry
