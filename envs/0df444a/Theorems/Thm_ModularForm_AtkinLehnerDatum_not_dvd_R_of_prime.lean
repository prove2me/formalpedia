-- Prove2me | Theorems.Thm_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime
-- name    : ModularForm.AtkinLehnerDatum.not_dvd_R_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/f71f1a63-9f8d-5d90-befc-aa4bca65f974
-- title:
--   The Atkin–Lehner prime q does not divide the cofactor R
-- statement:
--   Let $M$ and $q$ be natural numbers and let $W$ be an Atkin–Lehner datum for $(M,q)$, that is, a structure consisting of a natural number $R = W.R$ together with the factorisation $M = q\,R$, and two integers $a = W.a$, $b = W.b$ satisfying the Bézout relation $q\,a - R\,b = 1$ in $\mathbb{Z}$. Assume further that $q$ is prime. The conclusion is that $q$ does not divide $R$: there is no natural number $c$ with $R = q\,c$. Thus the Bézout datum forces $q$ and the cofactor $R$ to be coprime, which, combined with $M = q\,R$, is the condition that $q$ exactly divides $M$.
--
--   This records the coprimality $\gcd(q,R) = 1$, equivalently $q \parallel M$, implicit in the notion of an Atkin–Lehner datum at a prime $q$ dividing the level $M$. It is used to supply the non-divisibility hypothesis at the cofactor level, for instance in [`ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup`](thm.html#ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.AtkinLehnerDatum.not_dvd_R_of_prime {M q : ℕ}
    (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) : ¬ q ∣ W.R := by sorry
