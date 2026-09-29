-- Prove2me | Theorems.Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel
-- name    : FreyPackage.level_lowering_odd_prime_of_conductorLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/bfbcbe87-76e4-5719-8dab-3cb5c216248b
-- title:
--   Ribet level lowering at an odd prime q ≠ p
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p \ge 5$ with $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$, with associated Frey curve `P.freyCurve` over $\mathbb{Q}$. Let $N, q$ be naturals. Assume: (i) `P.IsConductorLevel N`, the project's predicate asserting $N > 0$, $N$ squarefree, and every prime divisor of $N$ divides $abc$ in $\mathbb{Z}$; (ii) $q$ is prime, $q \neq 2$, $q \neq p$ and $q \mid N$; (iii) `GaloisRepIsIrreducible` for `P.freyCurve` at $p$ over $K =$ `AlgebraicClosure ℚ`, which by definition says that the $\mathbb{Z}$-torsion submodule of $p$-torsion points of the Frey curve over $K$ is nontrivial and that its only $\mathbb{Z}/p$-submodules stable under all $\mathbb{Q}$-algebra automorphisms of $K$ are $\bot$ and $\top$; (iv) `P.ModularRepOfLevel N`, the project's congruence form of "the mod $p$ representation arises from level $N$": there are a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ which is a normalised eigenform in the project's sense (its $q$-expansion has $a_1 = 1$, is multiplicative on coprime indices and satisfies the usual recursions at prime powers, distinguishing primes dividing $N$ from those not), an integral Weierstrass model $W$ of `P.freyCurve` (some variable change over $\mathbb{Q}$ takes `P.freyCurve` to the base change of $W$), and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid N$ and $\ell \neq p$ the coefficient $a_\ell(f)$ is the image of an algebraic integer congruent modulo $\mathfrak{m}$ to the trace of Frobenius of the reduction of $W$ at $\ell$; (v) `P.GaloisRepUnramifiedAt q`, i.e. for every valuation subring $A$ of $K$ having $q$ among its nonunits, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ fixes every $p$-torsion point of the Frey curve over $K$. Then there exists $M \in \mathbb{N}$ with $M \mid N$, $q \nmid M$, and `P.ModularRepOfLevel M`.
--
--   This is Ribet's level-lowering theorem (the epsilon conjecture) in the shape needed for the Frey–Serre–Ribet argument, removing an odd prime $q \neq p$ from the level. Two differences from the textbook statement should be noted: the level is assumed squarefree and supported on the primes dividing $abc$ (so no reduction of a higher $q$-exponent is involved), and "the mod $p$ representation arises from level $M$" is the project's predicate `ModularRepOfLevel`, a congruence of Hecke eigenvalues with traces of Frobenius modulo a maximal ideal above $p$ in the algebraic integers, rather than an isomorphism of residual representations; the conclusion also only asserts $M \mid N$ and $q \nmid M$, with no claim about which divisor $M$ is. It is the inductive step used by [`FreyPackage.level_lowering_to_two_of_conductorLevel`](thm.html#FreyPackage.level_lowering_to_two_of_conductorLevel) to strip the primes $\neq p$ from a conductor-supported level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FreyPackage_IsConductorLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem FreyPackage.level_lowering_odd_prime_of_conductorLevel (P : FreyPackage) {N q : ℕ} (hcond : P.IsConductorLevel N) (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ P.p) (hqN : q ∣ N) (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) (hmod : P.ModularRepOfLevel N) (hunr : P.GaloisRepUnramifiedAt q) : ∃ M : ℕ, M ∣ N ∧ ¬ q ∣ M ∧ P.ModularRepOfLevel M := by sorry
