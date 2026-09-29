-- Prove2me | Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
-- name    : HopfAlgebra.finite_projective_hopfKer_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/136bd7c3-650f-5f20-b941-3fd6ef3cc4e4
-- title:
--   Kreimer–Takeuchi: A finite projective over the Hopf kernel
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $B$ be commutative rings carrying Hopf $R$-algebra structures, and assume that $B$ is finitely generated and free as an $R$-module. Let $\pi \colon A \to B$ be a morphism of $R$-bialgebras which is surjective as a map of sets. Form the Hopf kernel $\mathrm{hopfKer}\,\pi$: this is the $R$-subalgebra of $A$ on which the two $R$-algebra maps $A \to A \otimes_R B$ given by $a \mapsto (\mathrm{id}_A \otimes \pi)(\Delta a)$ and $a \mapsto a \otimes 1$ agree, i.e. the coinvariants $A^{\mathrm{co}\,\pi} = \{a \in A : (\mathrm{id}_A \otimes \pi)(\Delta a) = a \otimes 1\}$. The conclusion is the conjunction of two assertions about $A$ regarded as a module over the ring $\mathrm{hopfKer}\,\pi$: that it is a finite module, and that it is a projective module. No flatness, Noetherian or connectedness hypothesis is imposed on $R$, and no hypothesis beyond surjectivity is imposed on $\pi$.
--
--   This is the Kreimer–Takeuchi finiteness and projectivity theorem for a surjection of commutative Hopf algebras with finite free target; geometrically it says that for a finite locally free closed subgroup scheme $\operatorname{Spec} B$ of an affine group scheme $\operatorname{Spec} A$ over $\operatorname{Spec} R$, the quotient map to $\operatorname{Spec} A^{\mathrm{co}\,\pi}$ is finite locally free. It underlies the subsequent results on a retraction of $A$ onto the Hopf kernel together with the rank identity, on faithful flatness over a principal ideal base, and on the criterion for surjectivity of $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfAlgebra.finite_projective_hopfKer_of_surjective {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.Finite ↥(HopfAlgebra.hopfKer π) A ∧ Module.Projective ↥(HopfAlgebra.hopfKer π) A := by sorry
