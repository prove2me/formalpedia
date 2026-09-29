-- Prove2me | Theorems.Thm_FreyPackage_level_lowering_at_p_of_conductorLevel
-- name    : FreyPackage.level_lowering_at_p_of_conductorLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d1ad509f-d885-5731-8d18-ea79ae539535
-- title:
--   Mazur–Ribet level lowering at p for conductor levels
-- statement:
--   Let $P$ be a [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17), i.e. nonzero integers $a,b,c$ with $\gcd(a,b)=1$, $a\equiv 3 \bmod 4$, $b\equiv 0\bmod 2$, and a prime $p\ge 5$ with $a^p+b^p=c^p$; write $E=P.\mathrm{freyCurve}$ for the associated Weierstrass curve over $\mathbb{Q}$ with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. Let $N$ be a natural number which is a conductor level for $P$ in the project's sense (`IsConductorLevel`): $N>0$, $N$ is squarefree, and every prime $q\mid N$ satisfies $q\mid abc$ in $\mathbb{Z}$. Assume $p\mid N$; assume the irreducibility hypothesis `GaloisRepIsIrreducible` for $E$ and $p$ over $\mathbb{Q}$ with $K=\overline{\mathbb{Q}}$, which by definition says that the $\mathbb{Z}$-torsion submodule of $E(\overline{\mathbb{Q}})$ killed by $p$ is nontrivial and that every $\mathbb{Z}/p$-submodule of it stable under all $\sigma\in\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$ is $\bot$ or $\top$; and assume $P.\mathrm{ModularRepOfLevel}\ N$, which by definition asserts the existence of a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ satisfying the project's `IsNormalizedEigenform` conditions on its $q$-expansion coefficients (first coefficient $1$, multiplicativity at coprime indices, and the two prime-power recursions according as the prime divides $N$ or not), an integral Weierstrass model $W$ of $E$ (equal to $E$ up to a variable change over $\mathbb{Q}$), and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell\nmid \Delta_W$, $\ell\nmid N$ and $\ell\ne p$ there is an algebraic integer $a$ with $a=a_\ell(f)$ in $\mathbb{C}$ and $a\equiv \ell+1-\#W_{/\mathbb{F}_\ell}$ modulo $\mathfrak{m}$. The conclusion is that there exists $M$ with $M\mid N$, $p\nmid M$, and $P.\mathrm{ModularRepOfLevel}\ M$. Thus the congruence is realised at a level dividing $N$ and prime to $p$; no claim is made about an isomorphism of Galois representations, the datum being only the trace congruence modulo $\mathfrak{m}$ at good primes.
--
--   This is the level-lowering step at the residual characteristic itself, Ribet's theorem in the case $\ell=p$ (Mazur's principle at $p$ for finite flat residual representations), as in Ribet (1990) and Darmon–Diamond–Taylor §3.5. The formal statement differs from the textbook version in two ways: 'arises from level $N$' is the project's `ModularRepOfLevel`, a congruence of $q$-expansion coefficients with traces of Frobenius of an integral model modulo a maximal ideal above $p$ rather than an isomorphism of representations; and the level is assumed conductor-supported (squarefree with prime divisors dividing $abc$), so that $p^2\nmid N$ holds automatically and the bad primes of the integral model are controlled. It is used by [`FreyPackage.level_lowering_to_two_of_conductorLevel`](thm.html#FreyPackage.level_lowering_to_two_of_conductorLevel), which strips the primes dividing the level one at a time to reach a nonzero weight-$2$ cusp form on $\Gamma_0(2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean

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

theorem FreyPackage.level_lowering_at_p_of_conductorLevel (P : FreyPackage) {N : ℕ} (hcond : P.IsConductorLevel N) (hpN : P.p ∣ N) (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) (hmod : P.ModularRepOfLevel N) : ∃ M : ℕ, M ∣ N ∧ ¬ P.p ∣ M ∧ P.ModularRepOfLevel M := by sorry
