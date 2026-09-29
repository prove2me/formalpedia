-- Prove2me | Theorems.Thm_FreyPackage_mazurPrincipleAtPStep
-- name    : FreyPackage.mazurPrincipleAtPStep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a11f4deb-1642-51cc-a5c8-f7dca0cf1dc6
-- title:
--   One-step level lowering at p for the Frey curve
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p \ge 5$ such that $a^p + b^p = c^p$, $\gcd(a,b)=1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$; let $P.\mathtt{freyCurve}$ be the associated Weierstrass curve over $\mathbb{Q}$ with $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$, and let $P.\mathtt{freyCurveInt}$ be its integral model, whose base change along $\mathbb{Z} \to \mathbb{Q}$ is $P.\mathtt{freyCurve}$. The assertion is that $P$ satisfies the predicate `MazurPrincipleAtPStep`: for every natural number $M$, assume (i) that the $p$-torsion of the group of points of the Frey curve over $\overline{\mathbb{Q}}$ is nontrivial and that every $\mathbb{Z}/p$-submodule of it stable under the Galois action of $\mathbb{Q}$ is $\bot$ or $\top$; (ii) $M > 0$; (iii) $p \nmid M$; and (iv) that `ModularRepOfLevelAt` holds at level $Mp$, that is, there are a weight-two cusp form $f$ on $\Gamma_0(Mp)$ which is a normalized eigenform and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p \in \mathfrak{m}$, such that for every prime $\ell \ne p$ not dividing $Mp$ at which $P.\mathtt{freyCurveInt}$ has good reduction, the $\ell$-th $q$-coefficient of $f$ lies in the integral closure and is congruent mod $\mathfrak{m}$ to $a_\ell$ of that integral model. Then `ModularRepOfLevelAt` holds at level $M$, with the same meaning (primes $\ell \ne p$ not dividing $M$).
--
--   This is Mazur's principle in the form needed for Fermat's Last Theorem: it removes one factor of $p$ from the level of a weight-two eigenform giving rise to the mod $p$ representation of the Frey curve, under the hypothesis that this representation is irreducible. It is the inductive step used by [`FreyPackage.atPNewLoweringAtUniform`](thm.html#FreyPackage.atPNewLoweringAtUniform) in the level-lowering part of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_mazurPrincipleAtPStep.lean

import Mathlib
import Definitions.Def_FreyPackage_MazurPrincipleAtPStep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.mazurPrincipleAtPStep (P : FreyPackage) : P.MazurPrincipleAtPStep := by sorry
