-- Prove2me | Theorems.Thm_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective
-- name    : HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/830b100b-d91e-576f-af7e-7ba589a81816
-- title:
--   Rank multiplicativity for Hopf kernels of surjective bialgebra maps
-- statement:
--   Let $R$ be a commutative ring that is a domain, a principal ideal ring and of characteristic $0$. Let $A$ be a commutative ring carrying a Hopf $R$-algebra structure which is finite and free as an $R$-module and whose comultiplication is cocommutative, and let $B$ be a commutative ring carrying a Hopf $R$-algebra structure which is finite and free as an $R$-module (no cocommutativity assumed on $B$). Let $\pi \colon A \to B$ be a bialgebra homomorphism over $R$ which is surjective as a function. Write $\mathrm{hopfKer}\,\pi$ for the Hopf kernel, namely the $R$-subalgebra of $A$ on which the two algebra maps $A \to A \otimes_R B$ given by $\Delta_A$ followed by $\mathrm{id}_A \otimes \pi$ and by $a \mapsto a \otimes 1$ agree, i.e. $\{a \in A : (\mathrm{id} \otimes \pi)(\Delta a) = a \otimes 1\}$. Then the $R$-ranks satisfy $$\operatorname{finrank}_R(\mathrm{hopfKer}\,\pi)\cdot \operatorname{finrank}_R B = \operatorname{finrank}_R A.$$
--
--   This is the Hopf-algebra form of the multiplicativity of orders in an exact sequence of finite flat commutative group schemes, $|G| = |H|\cdot|G/H|$, for the closed subgroup scheme cut out by the Hopf kernel of a surjection. It is used in the construction of connected–étale sequences over $\mathbb{Z}_p$ and in rank bookkeeping for Hopf orders, and through these in the analysis of the Galois representations attached to torsion on elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finrank_hopfKer_mul_finrank_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.finrank_hopfKer_mul_finrank_of_surjective {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.finrank R ↥(HopfAlgebra.hopfKer π) * Module.finrank R B = Module.finrank R A := by sorry
