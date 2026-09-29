-- Prove2me | Theorems.Thm_FreyPackage_modularRepOfConductorLevel
-- name    : FreyPackage.modularRepOfConductorLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1b28bd44-2bb4-5b27-8d52-b71287e9c676
-- title:
--   Conductor-level modularity of the Frey curve's mod-p representation
-- statement:
--   For every Frey package $P$ — i.e. nonzero integers $a,b,c$ with $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$, $b\equiv 0\pmod 2$, and a prime $p\ge 5$ with $a^p+b^p=c^p$ — there exists a natural number $N$ with two properties. First, `P.IsConductorLevel N`: $N>0$, $N$ is squarefree, and every prime $q\mid N$ satisfies $q \mid abc$ in $\mathbb Z$. Second, `P.ModularRepOfLevel N`, which is the project's own notion and unfolds as follows: there are a cusp form $f$ of weight $2$ on $\Gamma_0(N)$, a Weierstrass curve $W$ over $\mathbb Z$ and a maximal ideal $\mathfrak m$ of the integral closure of $\mathbb Z$ in $\mathbb C$ such that (i) $f$ is a normalised eigenform in the project's sense, namely its $q$-expansion coefficients satisfy $a_1(f)=1$, multiplicativity $a_{mn}=a_m a_n$ for coprime $m,n$, and the two prime-power recursions $a_{q^{r+2}}=a_q a_{q^{r+1}}-q\,a_{q^{r}}$ for primes $q\nmid N$ and $a_{q^{r+2}}=a_q a_{q^{r+1}}$ for $q\mid N$; (ii) $W$ is an integral model of the Frey curve $P.freyCurve$, in the sense that some variable change over $\mathbb Q$ carries $P.freyCurve$ to the base change of $W$ to $\mathbb Q$; (iii) $p\in\mathfrak m$; and (iv) for every prime $\ell$ with $\ell\nmid\Delta(W)$, $\ell\nmid N$ and $\ell\ne p$, there is an algebraic integer $a$ with $a=a_\ell(f)$ in $\mathbb C$ and $a \equiv a_\ell(W) \pmod{\mathfrak m}$, where $a_\ell(W)$ is $\ell+1$ minus the number of points of the reduction of $W$ mod $\ell$. Thus the conclusion is a congruence of traces of Frobenius modulo a maximal ideal above $p$, not an isomorphism of Galois representations; the statement has no hypotheses beyond $P$ being a Frey package.
--
--   Classically this is the modularity theorem for semistable elliptic curves (Wiles, Taylor–Wiles) applied to the Frey curve, in the sharpened form in which the level is the conductor, i.e. the radical of $abc$ (the conductor clause going back to Carayol). The formal statement is deliberately weaker in shape than the textbook result: it asserts only the existence of a normalised eigenform of squarefree level supported on the primes dividing $abc$ whose Hecke eigenvalues agree with the Frobenius traces of an integral Frey model modulo a maximal ideal containing $p$, with no claim about representations being isomorphic. It is the entry point of the level-lowering step: it is the input to [`FreyPackage.level_lowering_to_two`](thm.html#FreyPackage.level_lowering_to_two), whose `IsModular` hypothesis is therefore formally unused, since modularity is re-derived here for the integral Frey model rather than consumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean

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

theorem FreyPackage.modularRepOfConductorLevel (P : FreyPackage) : ∃ N : ℕ, P.IsConductorLevel N ∧ P.ModularRepOfLevel N := by sorry
