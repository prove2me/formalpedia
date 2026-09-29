-- Prove2me | Theorems.Thm_FreyPackage_routeAReversePinBadOnlySeam
-- name    : FreyPackage.routeAReversePinBadOnlySeam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/5e8ae481-13ed-5cf2-bb2f-a70aa939e0b6
-- title:
--   Reverse-pin congruence at primes bad only for the witness model
-- statement:
--   Let $P$ be a Frey package: non-zero integers $a,b,c$, a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; write $E^{\mathrm{int}}=$ `freyCurveInt P` for the integral Weierstrass model with $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$. The theorem asserts, for this $P$, the following statement: for every level $N$, every cusp form $f$ of weight $2$ on $\Gamma_0(N)$, every Weierstrass curve $W$ over $\mathbb{Z}$ and every ideal $\mathfrak m$ of $\overline{\mathbb Z}=\mathrm{integralClosure}\ \mathbb Z\ \mathbb C$ such that $(N,f,W,\mathfrak m)$ is a congruent witness for $P$ — that is, $f$ is a normalised eigenform, $W$ satisfies `IsIntegralModelOf P.freyCurve`, $\mathfrak m$ is maximal and contains $p$, and for every prime $\ell$ with $\ell\nmid \Delta(W)$, $\ell\nmid N$, $\ell\ne p$ there is $a\in\overline{\mathbb Z}$ whose image in $\mathbb C$ is the $\ell$-th coefficient of the $q$-expansion of $f$ and with $a-\mathrm{tr}\,\mathrm{Frob}_\ell(W\bmod \ell)\in\mathfrak m$ — one has: for every prime $\ell$ with $\ell\nmid\Delta(E^{\mathrm{int}})$, $\ell\nmid N$, $\ell\ne p$ and $\ell\mid\Delta(W)$, there exists $a\in\overline{\mathbb Z}$ with $(a:\mathbb C)$ the $\ell$-th $q$-coefficient of $f$ and $a-\mathrm{tr}\,\mathrm{Frob}_\ell(E^{\mathrm{int}}\bmod\ell)\in\mathfrak m$.
--
--   This is the second residual case of the reverse pinning step: a congruent witness is given in terms of an arbitrary integral model $W$ of the Frey curve, and the congruence between the coefficients of $f$ and the Frobenius traces of the canonical integral model $E^{\mathrm{int}}$ must be produced also at the finitely many primes dividing $\Delta(W)$ but not $\Delta(E^{\mathrm{int}})$. It is used by [`FreyPackage.modularRepOfLevelNewAtPinned_of_newAt`](thm.html#FreyPackage.modularRepOfLevelNewAtPinned_of_newAt), where the congruence is transported to the canonical model; the assertion is vacuous when the witness model is already $E^{\mathrm{int}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_routeAReversePinBadOnlySeam.lean

import Definitions.Def_FreyPackage_RouteAReversePinSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.routeAReversePinBadOnlySeam (P : FreyPackage) : P.RouteAReversePinBadOnlySeam := by sorry
