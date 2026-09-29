-- Prove2me | Theorems.Thm_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr
-- name    : FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/89c76d53-86df-5b7d-b172-652469aea8fe
-- title:
--   Frey curve: p ∤ v₂(Δ) at the prime 2
-- statement:
--   Let $P$ be a Frey package: a triple of nonzero integers $a,b,c$ together with a prime $p \ge 5$ satisfying $a^p + b^p = c^p$, with $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$ and $b \equiv 0 \pmod 2$. Attached to $P$ is the integral Weierstrass curve `P.freyCurveInt` over $\mathbb{Z}$ with coefficients $a_1 = 1$, $a_2 = (b^p - 1 - a^p)/4$, $a_3 = 0$, $a_4 = -a^p b^p/16$, $a_6 = 0$ (the quotients being integer division), and $\Delta$ denotes its Weierstrass discriminant. The assertion is that the natural number $p$ does not divide the $2$-adic valuation $v_2(\Delta)$, taken in the sense of `padicValInt 2`, i.e. the exponent of $2$ in the factorisation of the integer $\Delta$. No further hypotheses beyond those packaged in the Frey package are imposed.
--
--   This is the arithmetic content of the statement that the mod-$p$ representation attached to the Frey curve is très ramifiée (not finite) at $2$, in Serre's terminology: the curve has multiplicative reduction at $2$ and the valuation of the minimal discriminant is not divisible by $p$. It is the reason the prime $2$ must be excluded from Ribet-style level lowering, and is used here in the construction of an element of inertia at $2$ acting non-trivially, [`FreyPackage.frey_exists_inertia_not_fixed_at_two`](thm.html#FreyPackage.frey_exists_inertia_not_fixed_at_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr.lean

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr (P : FreyPackage) : ¬ P.p ∣ padicValInt 2 P.freyCurveInt.Δ := by sorry
