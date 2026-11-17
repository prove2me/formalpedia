-- Prove2me | Theorems.Thm_N25_LocalFive_finite_algHom_of_finite_target
-- name    : N25.LocalFive.finite_algHom_of_finite_target
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:41.156468+00:00
-- url     : https://prove2.me/theorems/96e16727-7025-4136-9ffe-0e46de20d0d4
-- title:
--   A finite-type algebra has finitely many maps to a finite algebra
-- statement:
--   Let $R$, $A$, and $T$ be commutative rings, with $A$ and $T$ endowed with $R$-algebra structures. If $A$ is of finite type over $R$ and the underlying set of $T$ is finite, then the set of $R$-algebra homomorphisms from $A$ to $T$ is finite: $$|\mathrm{Hom}_{R\text{-alg}}(A,T)|<\infty.$$ This is the algebraic finiteness input for counting special-fiber points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

theorem N25.LocalFive.finite_algHom_of_finite_target
    {R A T : Type*}
    [CommRing R] [CommRing A] [CommRing T]
    [Algebra R A] [Algebra R T]
    [Algebra.FiniteType R A] [Finite T] :
    Finite (A →ₐ[R] T)  := by sorry
