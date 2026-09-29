-- Prove2me | Theorems.Thm_FreyCurve_four_dvd_card_reductionMod
-- name    : FreyCurve.four_dvd_card_reductionMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f6af2dca-bbc7-5ef4-8003-6c57b5e0ee5f
-- title:
--   4 divides #̃ E(𝔽_q) at good odd primes
-- statement:
--   Let $P$ be a Frey package, that is, nonzero integers $a,b,c$ together with a prime $p\ge 5$ satisfying $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$, and let `freyCurveInt P` be the associated Weierstrass curve over $\mathbb{Z}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$ (the quotients being integer division in $\mathbb{Z}$). Let $q$ be a prime with $q\neq 2$ which is a good prime for this curve in the sense of `IsGoodPrimeFor`, i.e. $q$ does not divide the discriminant $\Delta$ of `freyCurveInt P`. Then $4$ divides the cardinality, in the sense of `card`, of the reduction `reductionMod` of `freyCurveInt P` at $q$, namely the number of points of the associated affine curve over $\mathbb{Z}/q$ obtained by base change along $\mathbb{Z}\to\mathbb{Z}/q$; here the point set is `WeierstrassCurve.Affine.Point`, so the point at infinity is included in the count.
--
--   This is the divisibility consequence of the Frey curve having all of its $2$-torsion rational: the three finite $2$-division points have abscissae $0$, $a^p/4$, $-b^p/4$, which stay pairwise distinct modulo any odd prime of good reduction. It is used in the determination of the traces of Frobenius of the Frey curve at small primes, in particular by [`FreyCurve.freyCurveInt_apOfModel_three`](thm.html#FreyCurve.freyCurveInt_apOfModel_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyCurve_four_dvd_card_reductionMod.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FreyCurve

theorem four_dvd_card_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    4 ∣ ((FreyPackage.freyCurveInt P).reductionMod q).card := by sorry
