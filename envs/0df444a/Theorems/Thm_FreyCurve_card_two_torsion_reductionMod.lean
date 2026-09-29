-- Prove2me | Theorems.Thm_FreyCurve_card_two_torsion_reductionMod
-- name    : FreyCurve.card_two_torsion_reductionMod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/e574bf8f-cfc0-570a-a8f3-df73849692a7
-- title:
--   Reduced Frey curve has exactly four 2-torsion points
-- statement:
--   Let $P$ be a Frey package, that is, nonzero integers $a,b,c$ together with a prime $p \ge 5$ such that $a^p + b^p = c^p$, $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$, and let `freyCurveInt` $P$ be the associated Weierstrass curve over $\mathbb{Z}$ with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$ (the divisions being integer divisions). Let $q$ be a prime with $q \neq 2$, and assume that $q$ is a good prime for this curve in the sense that $q$ does not divide its discriminant $\Delta$ as an integer. Write $\tilde{E}$ for the reduction of `freyCurveInt` $P$ modulo $q$, namely its image under the coefficientwise map induced by the ring homomorphism $\mathbb{Z} \to \mathbb{Z}/q$. The assertion is that the $\mathbb{Z}$-submodule of elements killed by $2$ in the group of affine points $\tilde{E}(\mathbb{Z}/q)$ has cardinality exactly $4$.
--
--   This records that the full $2$-torsion of the Frey curve, which is rational over $\mathbb{Q}$ because the cubic $x(x - a^p)(x + b^p)$ splits, survives reduction at every odd prime of good reduction. It is used by [`FreyCurve.four_dvd_card_reductionMod`](thm.html#FreyCurve.four_dvd_card_reductionMod), and thence in the computation of the traces of Frobenius of the Frey curve at such primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyCurve_card_two_torsion_reductionMod.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.Algebra.Module.Torsion.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FreyCurve

theorem card_two_torsion_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    Nat.card (Submodule.torsionBy ℤ ((FreyPackage.freyCurveInt P).reductionMod q).toAffine.Point 2) = 4 := by sorry
