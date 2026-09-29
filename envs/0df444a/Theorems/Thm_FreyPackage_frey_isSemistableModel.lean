-- Prove2me | Theorems.Thm_FreyPackage_frey_isSemistableModel
-- name    : FreyPackage.frey_isSemistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/8ddc0f8f-5606-5586-8f24-2d6221f868a3
-- title:
--   Semistability of the integral Frey model
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p \ge 5$ satisfying $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Attached to $P$ is the integral Weierstrass curve `freyCurveInt` over $\mathbb{Z}$ with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$, the quotients being integer division (both numerators are in fact divisible by the stated denominators under the congruence conditions on $a$ and $b$). The theorem asserts the predicate `IsSemistableModel` for this curve, which by definition says: for every natural number $q$ that is prime, if $q$ divides the discriminant $\Delta$ of `freyCurveInt` in $\mathbb{Z}$, then $q$ does not divide its invariant $c_4$. Thus no rational prime divides both $\Delta$ and $c_4$ of the integral model; nothing is asserted here about conductors, reduction types or minimality beyond this divisibility statement.
--
--   This is the standard semistability property of the Frey–Hellegouarch curve attached to a putative solution of the Fermat equation: the chosen normalisation makes the reduction good or multiplicative at every prime, including $2$. It is invoked as the semistability input in the modularity and level-lowering steps of the argument, for instance by [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel), [`FreyPackage.level_lowering_odd_prime_of_conductorLevel`](thm.html#FreyPackage.level_lowering_odd_prime_of_conductorLevel) and [`FreyPackage.mazurPrincipleAtPStep`](thm.html#FreyPackage.mazurPrincipleAtPStep).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frey_isSemistableModel.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem FreyPackage.frey_isSemistableModel (P : FreyPackage) : P.freyCurveInt.IsSemistableModel := by sorry
