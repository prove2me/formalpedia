-- Prove2me | Theorems.Thm_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
-- name    : HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/ea7b6221-be95-5186-8761-36878ca06b28
-- title:
--   Local ring from reduced Cartier dual of p-power rank
-- statement:
--   Let $k$ be an algebraically closed field and $p$ a prime with $k$ of characteristic $p$. Let $N$ be a commutative ring equipped with the structure of a Hopf algebra over $k$ whose comultiplication is cocommutative, and assume $N$ is finite as a $k$-module. Write [`CartierDual k N`](def/HopfAlgebra_CartierDual.html#L12) for the $k$-linear dual $\operatorname{Hom}_k(N,k)$ of $N$, with the commutative ring structure coming from the bialgebra structure of $N$. Assume that this Cartier dual is a reduced ring, and that there is a natural number $m$ with $\dim_k N = p^m$ (the Lean hypothesis is $\mathrm{finrank}_k N = p^m$). Then the conclusion is that $N$ is a local ring, i.e. `IsLocalRing N`: $N$ is nontrivial and has a unique maximal ideal. No assertion is made about which ideal this is, although the proof identifies it as the kernel of the counit.
--
--   In the language of group schemes: a finite commutative group scheme $G=\operatorname{Spec} N$ of $p$-power order over an algebraically closed field of characteristic $p$ whose Cartier dual is étale (multiplicative type) is infinitesimal, so $N$ is local. It feeds into the study of ordinary finite flat $p$-group schemes over the valuation ring of an algebraic closure, being cited in the analysis of Hopf algebra maps that are trivial modulo the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (N : Type v) [CommRing N] [HopfAlgebra k N] [Coalgebra.IsCocomm k N] [Module.Finite k N]
    (hred : IsReduced (CartierDual k N)) (m : ℕ) (hN : Module.finrank k N = p ^ m) :
    IsLocalRing N := by sorry
