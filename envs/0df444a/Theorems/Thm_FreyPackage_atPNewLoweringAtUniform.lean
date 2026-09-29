-- Prove2me | Theorems.Thm_FreyPackage_atPNewLoweringAtUniform
-- name    : FreyPackage.atPNewLoweringAtUniform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/0d32ca9a-ec05-5e4a-a01a-432cd4f30e9b
-- title:
--   At-p level lowering for pinned p-new witnesses
-- statement:
--   Let $P$ be a Frey package: nonzero integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, with associated Frey curve $E=$ `P.freyCurve` over $\mathbb{Q}$ and integral model `freyCurveInt P`. The theorem asserts the predicate `AtPNewLoweringAtUniform` for $P$, namely: for every natural number $N_0$ with $0<N_0$ and $p\nmid N_0$, assume (i) `GaloisRepIsIrreducible` for $E$ and $p$ over $\mathbb{Q}$ with coefficients in $\overline{\mathbb{Q}}$, i.e. the $p$-torsion submodule of $E(\overline{\mathbb{Q}})$ is nontrivial and every Galois-stable $\mathbb{Z}/p$-submodule of it is $\bot$ or $\top$; (ii) $p \mid v_p(\Delta_E)$, the $p$-adic valuation of the discriminant of $E$; and (iii) `ModularRepOfLevelNewAtPinned` at level $N_0p$ and $q=p$: there are a weight-$2$ cusp form $g$ on $\Gamma_0(N_0p)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p\in\mathfrak{m}$, such that $g$ is a normalised eigenform, $g$ is new at $p$, and for every prime $\ell$ that is a good prime for `freyCurveInt P`, does not divide $N_0p$ and differs from $p$, the $\ell$-th $q$-coefficient of $g$ is an algebraic integer congruent mod $\mathfrak{m}$ to $a_\ell$ of that integral model. Then `ModularRepOfLevelAt` holds for $N_0$: there are a weight-$2$ normalised eigenform $f$ on $\Gamma_0(N_0)$ and a maximal ideal $\mathfrak{m}$ containing $p$ with the same congruence of $\ell$-th coefficients with $a_\ell$ of `freyCurveInt P` for all primes $\ell$ good for that model with $\ell\nmid N_0$ and $\ell\ne p$.
--
--   This is the level-lowering step at $p$ for the Frey curve, in the shape in which both the input and the output modularity witness are pinned to the canonical integral Frey model: a $p$-new eigenform of level $N_0p$ matching the mod-$p$ representation is replaced by an eigenform of level $N_0$. It is invoked by [`FreyPackage.atPNewLowering`](thm.html#FreyPackage.atPNewLowering).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_atPNewLoweringAtUniform.lean

import Mathlib
import Definitions.Def_FreyPackage_LoweringAtUniform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.atPNewLoweringAtUniform (P : FreyPackage) : P.AtPNewLoweringAtUniform := by sorry
