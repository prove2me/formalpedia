-- Prove2me | Theorems.Thm_FreyCurve_isPeuRamifieeAt_odd_of_integralForm
-- name    : FreyCurve.isPeuRamifieeAt_odd_of_integralForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/25cbbe0c-7103-5583-a17d-1ab3926eeeb6
-- title:
--   Frey curve is peu ramifiée at every odd prime
-- statement:
--   Let $P$ be a [`FreyPackage`](def/FLTPrelim_FreyPackage.html#L17): nonzero integers $a,b,c$, a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$. Let $q$ be a natural number carrying the typeclass assumption `Fact q.Prime`, and assume $q\neq 2$. The conclusion is `P.freyCurve.IsPeuRamifieeAt P.p q`, where `P.freyCurve` is the Weierstrass curve over $\mathbb{Q}$ with coefficients $a_1=1$, $a_2=(b^p-1-a^p)/4$, $a_3=0$, $a_4=-a^pb^p/16$, $a_6=0$ (the division being carried out in $\mathbb{Q}$), and where the project's predicate [`WeierstrassCurve.IsPeuRamifieeAt W p \ell`](def/WeierstrassCurve_PeuRamifiee.html#L10) is by definition the single divisibility $(p:\mathbb{Z}) \mid \operatorname{padicValRat} \ell\, W.\Delta$. So the assertion is exactly: the $q$-adic valuation of the discriminant $\Delta$ of the Frey curve, computed as a rational number by Mathlib's `padicValRat`, is divisible by $p$. Two points about the shape of the statement should be noted. First, despite the name, `IsPeuRamifieeAt` is not a statement about a Galois representation or about finite-flatness: it is literally the above congruence condition on the discriminant valuation, which classically encodes "peu ramifié" only in conjunction with multiplicative reduction. Second, despite the suffix `of_integralForm`, the statement mentions neither `P.freyCurveInt` nor any integral model; it is a statement about the rational Weierstrass model `P.freyCurve`. No hypothesis beyond $q\neq 2$ and primality of $q$ is imposed on $q$; in particular $q=p$ is allowed, and $q$ need not divide $abc$.
--
--   Classically this is the valuation computation underlying Serre's criterion (Duke Math. J. 54 (1987), §2.8–2.9) that the mod-$p$ representation attached to the Frey curve is peu ramifié, equivalently of Serre weight $2$, at all odd primes; the formal statement records only the arithmetic half, namely $p \mid v_q(\Delta)$, and leaves the translation into a condition on the representation to the consumers of the predicate. Within the project it serves as the "finite at $p$" input to level lowering: it is used by [`FreyPackage.level_lowering_at_p_of_conductorLevel`](thm.html#FreyPackage.level_lowering_at_p_of_conductorLevel), the Mazur–Ribet step removing the prime $p$ from the level, and through it by [`FreyPackage.mazurPrincipleAtPStep`](thm.html#FreyPackage.mazurPrincipleAtPStep). The same divisibility, at odd $q \neq p$, is what elsewhere feeds the unramifiedness hypothesis in Ribet's level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyCurve_isPeuRamifieeAt_odd_of_integralForm.lean

import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open FreyPackage
namespace FreyCurve

theorem isPeuRamifieeAt_odd_of_integralForm (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) : P.freyCurve.IsPeuRamifieeAt P.p q := by sorry
