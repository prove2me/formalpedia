-- Prove2me | Theorems.Thm_FreyPackage_atPNewLowering
-- name    : FreyPackage.atPNewLowering
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/6262876b-59db-54fe-897e-547880da0bcd
-- title:
--   Level lowering at p for p-new modular witnesses
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ with $a^p+b^p=c^p$ for a prime $p\ge 5$, with $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b$ even, and write $p=P.p$ and $E=P.\mathtt{freyCurve}$ for the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. The theorem asserts the closed proposition `P.AtPNewLowering`, which unfolds as follows: for every natural number $N_0$ with $0<N_0$ and $p\nmid N_0$, assume (i) `GaloisRepIsIrreducible` for $E$ at $p$ over $\mathbb{Q}$ with $K=\mathrm{AlgebraicClosure}\ \mathbb{Q}$, that is, the $\mathbb{Z}$-torsion submodule of $p$-torsion points of $E$ over $\overline{\mathbb{Q}}$ is nontrivial and every $\mathbb{Z}/p$-submodule of it stable under the action of all $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ equals $\bot$ or $\top$; (ii) $E.\mathtt{IsPeuRamifieeAt}\ p\ p$, which by definition says that $p$ divides the $p$-adic valuation $\mathrm{padicValRat}\ p\ \Delta_E$ of the discriminant of this Weierstrass model; and (iii) `P.ModularRepOfLevelNewAt (N₀ * P.p) P.p`, namely that there are a weight-$2$ cusp form $g$ for $\Gamma_0(N_0p)$, a Weierstrass curve $W$ over $\mathbb{Z}$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ such that $P.\mathtt{IsCongruentWitness}$ holds ($g$ satisfies the project's normalised-eigenform conditions on its $q$-coefficients, $W$ becomes $E$ after a variable change over $\mathbb{Q}$, $\mathfrak{m}$ is maximal with $p\in\mathfrak{m}$, and for every prime $\ell$ with $\ell\nmid\Delta_W$, $\ell\nmid N_0p$, $\ell\neq p$ the coefficient $a_\ell(g)$ is an algebraic integer congruent mod $\mathfrak{m}$ to the Frobenius trace $a_\ell(W)$ of the reduction of $W$), together with the project's $p$-newness clause $a_p(g)^2=1$. The conclusion is `P.ModularRepOfLevel N₀`: the same package of data — a normalised eigenform of weight $2$ for $\Gamma_0(N_0)$, an integral model of $E$, and a maximal ideal above $p$ with the same Frobenius-trace congruences at all good primes $\ell\nmid N_0$, $\ell\neq p$ — exists at level $N_0$.
--
--   This is the level-lowering step at the residue characteristic itself: Mazur's principle in the form due to Ribet, in the case $q=p$, where the hypothesis of unramifiedness at the auxiliary prime is replaced by the local condition at $p$ that the representation be peu ramifiée in Serre's sense. In the formalisation the peu-ramifiée condition is taken in the concrete shape '$p$ divides $v_p(\Delta)$' for the given Frey model, $p$-newness of the source form is the numerical clause $a_p^2=1$, and modularity of a mod-$p$ system is recorded as the existence of a normalised eigenform whose $q$-coefficients are congruent to Frobenius traces modulo a maximal ideal above $p$; so both hypothesis and conclusion are statements about such congruence witnesses rather than about Galois representations directly. It is used by [`FreyPackage.level_lowering_at_p_of_conductorLevel`](thm.html#FreyPackage.level_lowering_at_p_of_conductorLevel), which, for a Frey package whose conductor level $N$ is divisible by $p$, produces a divisor $M\mid N$ with $p\nmid M$ carrying the same modular witness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_atPNewLowering.lean

import Definitions.Def_FreyPackage_AtPNewLowering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup
namespace FreyPackage

theorem atPNewLowering (P : FreyPackage) : P.AtPNewLowering := by sorry
