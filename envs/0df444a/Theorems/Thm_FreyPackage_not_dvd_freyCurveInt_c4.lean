-- Prove2me | Theorems.Thm_FreyPackage_not_dvd_freyCurveInt_c4
-- name    : FreyPackage.not_dvd_freyCurveInt_c4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2c1dcaa6-4918-5962-867d-f3439bcd2a71
-- title:
--   At primes dividing abc, c₄ of the Frey model is a unit
-- statement:
--   Let $P$ be a Frey package, i.e. nonzero integers $a,b,c$ together with a prime $p\ge 5$ such that $a^{p}+b^{p}=c^{p}$, $\gcd(a,b)=1$, $a\equiv 3 \pmod 4$ and $b\equiv 0\pmod 2$; write $W=P.\mathrm{freyCurveInt}$ for the integral Weierstrass model over $\mathbb{Z}$ with coefficients $a_1=1$, $a_2=(b^{p}-1-a^{p})/4$, $a_3=0$, $a_4=-a^{p}b^{p}/16$, $a_6=0$, the quotients being taken in $\mathbb{Z}$ (they are in fact exact). Let $q$ be a prime natural number whose image in $\mathbb{Z}$ divides the product $abc$. The assertion is that $q$ does not divide the invariant $c_4$ of $W$, where $c_4=b_2^{2}-24b_4$ is the usual Weierstrass invariant of an integral model. In the course of the proof this invariant is identified with $a^{2p}+a^{p}b^{p}+b^{2p}$, equivalently with $c^{2p}-(ab)^{p}$.
--
--   This is the arithmetic half of the statement that the Frey curve attached to a Frey package has multiplicative (rather than additive) reduction at every prime dividing $abc$, the integral model being minimal there; combined with $q\mid\Delta(W)$ it gives semistability away from $2$. It is used in the analysis of the local behaviour of the mod $p$ representation, for instance in [`FreyPackage.frey_exists_inertia_not_fixed_at_two`](thm.html#FreyPackage.frey_exists_inertia_not_fixed_at_two) and [`FreyPackage.frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line`](thm.html#FreyPackage.frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_not_dvd_freyCurveInt_c4.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.not_dvd_freyCurveInt_c4 (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hqabc : (q : ℤ) ∣ P.a * P.b * P.c) : ¬ (q : ℤ) ∣ P.freyCurveInt.c₄ := by sorry
