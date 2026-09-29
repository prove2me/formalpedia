-- Prove2me | Theorems.Thm_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois
-- name    : HopfAlgebra.natCard_algHom_eq_mul_of_isHopfGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/f9342625-c420-5b06-a03e-bd078112f9d1
-- title:
--   Multiplicativity of point counts along a Hopf–Galois quotient
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $B$ be commutative rings equipped with $R$-bialgebra structures, with $A$ finite as an $R$-module, let $k$ be an algebraically closed field which is an $R$-algebra, and let $\pi \colon A \to B$ be a homomorphism of $R$-bialgebras. Write $\rho =$ `coaction` $\pi$ for the composite of the comultiplication $A \to A \otimes_R A$ with $\mathrm{id}_A \otimes \pi$, and let `hopfKer` $\pi \subseteq A$ be the $R$-subalgebra on which $\rho$ agrees with $a \mapsto a \otimes 1$. Assume `IsHopfGalois` $\pi$: the $R$-linear map `canMap` $\pi$ underlying the canonical algebra homomorphism `canAlgHom` $\pi \colon A \otimes_R A \to A \otimes_R B$ is surjective, and every $z$ in its kernel lies in the $R$-submodule spanned by the balancing relations, i.e. by the elements $(ah) \otimes a' - a \otimes (h a')$ with $a, a' \in A$ and $h \in$ `hopfKer` $\pi$. Then the natural-number cardinalities of the sets of $R$-algebra homomorphisms into $k$ satisfy $$\#(A \to_{R} k) = \#(B \to_{R} k) \cdot \#(\mathrm{hopfKer}\,\pi \to_{R} k).$$ The equality is of `Nat.card`s, and it is obtained from an explicit bijection $(A \to_R k) \simeq (B \to_R k) \times (\mathrm{hopfKer}\,\pi \to_R k)$.
--
--   In the geometric dictionary this is the multiplicativity $\#G(k) = \#H(k)\cdot\#(G/H)(k)$ of point counts over an algebraically closed field for a finite group scheme $G = \operatorname{Spec} A$ with quotient map onto $\operatorname{Spec} B$, stated for an arbitrary Hopf–Galois bialgebra homomorphism rather than for group schemes. It is used for the point counts underlying the exactness statement [`HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two`](thm.html#HopfAlgebra.exists_bialgHom_surjective_range_eq_hopfKer_of_exact_of_ne_two) and in [`HopfAlgebra.natCard_algHom_eq_mul_of_surjective`](thm.html#HopfAlgebra.natCard_algHom_eq_mul_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w x

theorem HopfAlgebra.natCard_algHom_eq_mul_of_isHopfGalois
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    [Module.Finite R A] (k : Type x) [Field k] [IsAlgClosed k] [Algebra R k]
    (π : A →ₐc[R] B) (hHG : HopfAlgebra.IsHopfGalois π) :
    Nat.card (A →ₐ[R] k) = Nat.card (B →ₐ[R] k) * Nat.card (↥(HopfAlgebra.hopfKer π) →ₐ[R] k) := by sorry
