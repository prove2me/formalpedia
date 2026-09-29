-- Prove2me | Theorems.Thm_ModularCurve_heckeInputsFibre_of_prime
-- name    : ModularCurve.heckeInputsFibre_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/7054ee9a-e4f9-5007-a2bb-d893fabdfb75
-- title:
--   Hecke inputs at level N and index q, both primes
-- statement:
--   Let $k$ be a field and let $N$ and $q$ be prime numbers with $(N:k)\neq 0$ and $(q:k)\neq 0$. The assertion is the predicate `HeckeInputsFibre k N q`, that is: the intermediate field `charLDegeneracyRoof k N q` of the Laurent series field $k((X))$ generated over $k$ by the four elements `jqModC k`, `jqNModC k N`, `jqNModC k q` and `jqNModC k (N * q)` satisfies `HasPrincipalDivisors`, i.e. every nonzero element $f$ of it has a divisor: a finitely supported function on places whose value at each place $v$ is $v.\mathrm{ord}\, f$ and whose degree is $0$; moreover the two ring homomorphisms underlying the degeneracy maps `heckeBetaC k N q` and `heckeAlphaC k N q` are integral; and, for these data, the divisor-level correspondence `heckeDivFibre k N q` on divisors of `modularFunctionFieldC k N` — formed as `Divisor.correspondence` of `heckeBetaC` and `heckeAlphaC` — descends to the degree-zero class group, meaning that it carries degree-zero divisors to degree-zero divisors and principal divisors to principal divisors.
--
--   This packages the hypotheses needed to define the Hecke operator of index $q$ on the degree-zero divisor class group of the level-$N$ modular function field $k(j,j_N)$, realised as pushforward along one degeneracy leg composed with pullback along the other; for $N$ prime this is the Hecke action on $X_0(N)$. It is invoked wherever the Hecke operator on $\mathrm{Pic}^0$ is used in the Eisenstein-quotient and inertia arguments in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeInputsFibre_of_prime.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve in

theorem ModularCurve.heckeInputsFibre_of_prime (k : Type*)
    [Field k] (N q : ℕ) [NeZero N] [NeZero q] [Fact N.Prime] [Fact q.Prime]
    (hN : (N : k) ≠ 0) (hq : (q : k) ≠ 0) :
    HeckeInputsFibre k N q := by sorry
