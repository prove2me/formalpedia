-- Prove2me | Theorems.Thm_FreyPackage_padicValInt_freyCurveInt_discr
-- name    : FreyPackage.padicValInt_freyCurveInt_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/bc1710d7-3bf8-5dff-aa1a-1c7b2fad6ffe
-- title:
--   q-adic valuation of the integral Frey discriminant at odd q
-- statement:
--   Let $P$ be a Frey package, that is: nonzero integers $a,b,c$, a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0 \pmod 2$. Write $W=$ `P.freyCurveInt` for the associated integral Weierstrass model over $\mathbb{Z}$, given by the coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$ (the quotients being taken in $\mathbb{Z}$), and let $\Delta$ denote its discriminant in the sense of Mathlib's Weierstrass curves. Let $q$ be a prime natural number with $q\neq 2$. The assertion is the equality of $q$-adic valuations of integers $$v_q(\Delta(W)) = 2p\, v_q(abc),$$ where $v_q$ is `padicValInt q`, the $q$-adic valuation of an integer computed through its absolute value. Nothing is asserted at $q=2$.
--
--   This is the valuation form of the computation $\Delta_{\min}=2^{-8}(abc)^{2p}$ for the Frey curve attached to a putative solution of Fermat's equation, as in Darmon–Diamond–Taylor, Theorem 2.15: away from $2$ the discriminant of the integral model is a perfect $2p$-th power up to units. It feeds [`FreyPackage.p_dvd_padicValInt_freyCurveInt_discr`](thm.html#FreyPackage.p_dvd_padicValInt_freyCurveInt_discr), the divisibility $p \mid v_q(\Delta)$ at odd primes of bad reduction used for the unramifiedness of the mod $p$ representation outside $2p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_padicValInt_freyCurveInt_discr.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.padicValInt_freyCurveInt_discr (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    padicValInt q P.freyCurveInt.Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) := by sorry
