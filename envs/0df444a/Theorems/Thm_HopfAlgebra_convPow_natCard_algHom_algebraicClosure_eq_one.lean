-- Prove2me | Theorems.Thm_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one
-- name    : HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/bdf8a118-9be5-5693-b2f4-faf9bf03788f
-- title:
--   Finite flat group schemes over ℤ are killed by their order
-- statement:
--   Let $K$ be a commutative ring equipped with a Hopf algebra structure over $\mathbb Z$ which is of finite type as a $\mathbb Z$-algebra and flat as a $\mathbb Z$-module, and put $N := \#\operatorname{Hom}_{\mathbb Z\text{-alg}}(K,\overline{\mathbb Q})$, the cardinality of the set of $\mathbb Z$-algebra homomorphisms from $K$ into the algebraic closure `AlgebraicClosure ℚ` of $\mathbb Q$, taken as a natural number via `Nat.card` (so $N=0$ when that set is infinite). Let $T$ be any commutative ring and let $f$ be a $\mathbb Z$-algebra homomorphism $K \to T$, viewed as an element of the convolution monoid `WithConv (K →ₐ[ℤ] T)` of such homomorphisms, whose multiplication is convolution through the comultiplication of $K$ and whose unit is the counit of $K$ followed by the structure map $\mathbb Z \to T$. Then the $N$-th convolution power of $f$ equals that unit element. Equivalently: the affine group scheme $\operatorname{Spec} K$ over $\mathbb Z$ is killed by the number of its $\overline{\mathbb Q}$-valued points, the assertion being vacuous when there are infinitely many such points.
--
--   This is the elementary, flat-over-$\mathbb Z$ case of Deligne's theorem that a commutative finite locally free group scheme of order $n$ is killed by $n$, the order being read off here from the geometric points in characteristic zero; the proof invokes Cartier's theorem [`HopfAlgebra.isReduced_of_finiteType_of_charZero`](thm.html#HopfAlgebra.isReduced_of_finiteType_of_charZero) that a finite-type commutative Hopf algebra over a field of characteristic zero is reduced. It feeds the structural results [`HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two`](thm.html#HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_ne_two) and [`HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two`](thm.html#HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two), which identify such Hopf algebras with monoid algebras once the number of geometric points is prescribed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (T : Type v) [CommRing T] (f : WithConv (K →ₐ[ℤ] T)) :
    f ^ Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 1 := by sorry
