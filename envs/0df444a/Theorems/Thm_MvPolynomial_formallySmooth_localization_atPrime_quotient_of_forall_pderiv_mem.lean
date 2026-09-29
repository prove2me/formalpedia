-- Prove2me | Theorems.Thm_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
-- name    : MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/3da9e14d-9a7c-5ff9-b5e1-612e5192c259
-- title:
--   Jacobian criterion for formal smoothness of a localised quotient
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $n$ be a natural number, and let $I \le J$ be ideals of the polynomial ring $R[X_i]_{i \in \mathrm{Fin}\,n}$ (`MvPolynomial (Fin n) R`) with $J$ maximal. Assume the Jacobian-type condition: for every $v \in I$ such that all the partial derivatives $\partial v/\partial X_i$ (the operators `MvPolynomial.pderiv i`, $i \in \mathrm{Fin}\,n$) lie in $J$, one has $v \in J \cdot I$. Since the kernel of the quotient map $R[X_i] \to R[X_i]/I$ is $I$ and $I \le J$, the image $J' = J \cdot (R[X_i]/I)$ of $J$ under `Ideal.Quotient.mk I` is a prime ideal of $R[X_i]/I$; the statement records this primality instance and then asserts that the localisation of $R[X_i]/I$ at the prime $J'$, i.e. `Localization.AtPrime (J.map (Ideal.Quotient.mk I))`, is a formally smooth $R$-algebra in the sense of `Algebra.FormallySmooth`.
--
--   This is the Jacobian criterion for smoothness in its ring-theoretic, formally smooth form: a local ring of a finitely presented $R$-algebra at a maximal-type prime is formally smooth over $R$ once the Jacobian condition holds at that prime. It underlies the two criteria [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_charP_of_finiteType_int) and [`AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing`](thm.html#AlgebraicGeometry.Smooth.of_forall_exists_lift_of_isArtinianRing_of_isNoetherianRing), which deduce smoothness of a scheme morphism from a lifting property against Artinian test rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial IsLocalRing

theorem MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) [hJ : J.IsMaximal]
    (hJac : ∀ v ∈ I, (∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) → v ∈ J * I) :
    haveI : (J.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hIJ)
    Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) := by sorry
