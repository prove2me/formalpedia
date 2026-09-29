-- Prove2me | Theorems.Thm_FreyPackage_padicValInt_two_freyCurveInt_discr
-- name    : FreyPackage.padicValInt_two_freyCurveInt_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/09e9ceab-f530-5d62-b013-0ef720c078db
-- title:
--   Two-adic valuation of the integral Frey discriminant
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p\ge 5$ such that $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$. Attached to $P$ is the integral Weierstrass model `freyCurveInt` over $\mathbb{Z}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-(a^pb^p)/16$ and $a_6=0$, the two quotients being taken in $\mathbb{Z}$ (they are exact divisions under the above congruences). Write $\Delta$ for its discriminant. The assertion is the equality of natural numbers
--   $$v_2(\Delta)+8 = 2p\,v_2(abc),$$
--   where $v_2$ denotes `padicValInt 2`, the $2$-adic valuation of an integer. Since the statement lives in $\mathbb{N}$, the classical relation $v_2(\Delta)=2p\,v_2(abc)-8$ is recorded in the additive form above; as $a$ and $c$ are odd, $v_2(abc)=v_2(b)$.
--
--   This is the $2$-adic half of the standard valuation computation for the discriminant of the Frey curve, as in Darmon–Diamond–Taylor, Theorem 2.15. It is used to show that $p$ does not divide $v_2(\Delta)$, and thence that inertia at $2$ does not act trivially on the relevant $p$-torsion, by [`FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr`](thm.html#FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr) and [`FreyPackage.frey_exists_inertia_not_fixed_at_two`](thm.html#FreyPackage.frey_exists_inertia_not_fixed_at_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_padicValInt_two_freyCurveInt_discr.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.padicValInt_two_freyCurveInt_discr (P : FreyPackage) :
    padicValInt 2 P.freyCurveInt.Δ + 8 = 2 * P.p * padicValInt 2 (P.a * P.b * P.c) := by sorry
