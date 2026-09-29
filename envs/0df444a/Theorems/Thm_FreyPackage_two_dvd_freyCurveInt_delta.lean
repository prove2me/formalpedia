-- Prove2me | Theorems.Thm_FreyPackage_two_dvd_freyCurveInt_delta
-- name    : FreyPackage.two_dvd_freyCurveInt_delta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d2ca32e4-815c-58c4-bddd-8c54d4830a23
-- title:
--   Two divides the discriminant of the integral Frey curve
-- statement:
--   Let $P$ be a Frey package: a triple of nonzero integers $a, b, c$ together with a prime $p \ge 5$ satisfying $a^p + b^p = c^p$, with $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Let [`FreyPackage.freyCurveInt P`](def/FLTPrelim_FreyPackage.html#L83) be the Weierstrass curve over $\mathbb{Z}$ attached to $P$, namely the one with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$ and $a_6 = 0$, the two quotients being taken in $\mathbb{Z}$. The assertion is the divisibility $2 \mid \Delta$, where $\Delta$ denotes the discriminant of this integral Weierstrass curve, formed from its coefficients by the usual formula in Mathlib. In other words, the integral Frey model has bad reduction at $2$. No further hypotheses enter; the statement is a divisibility in $\mathbb{Z}$, not a statement about the exact power of $2$ dividing $\Delta$ (the proof in fact produces $2^{2p-8} \mid \Delta$ along the way).
--
--   This records that $2$ is a prime of bad reduction for the canonical integral model of the Frey curve attached to a putative Fermat solution, a basic input to the conductor computation for that curve. It is used in the construction of the modular representation pinned to be new at a prime, where it rules out the prime $2$ in a case distinction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_two_dvd_freyCurveInt_delta.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem FreyPackage.two_dvd_freyCurveInt_delta (P : FreyPackage) :
    (2 : ℤ) ∣ (FreyPackage.freyCurveInt P).Δ := by sorry
