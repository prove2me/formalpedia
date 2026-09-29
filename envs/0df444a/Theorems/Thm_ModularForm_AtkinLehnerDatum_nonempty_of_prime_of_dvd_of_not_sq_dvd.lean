-- Prove2me | Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
-- name    : ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/18b684b8-596b-5a86-9089-cb99e042dc3f
-- title:
--   Existence of an Atkin–Lehner datum at a prime exactly dividing the level
-- statement:
--   Let $M$ and $q$ be natural numbers with $q$ prime, $q \mid M$ and $q^2 \nmid M$. Then the type [`ModularForm.AtkinLehnerDatum M q`](def/ModularForm_AtkinLehnerDatum.html#L14) is nonempty, i.e. there exists a quadruple consisting of a natural number $R$, a proof that $M = q R$, and integers $a$, $b$ satisfying the Bézout relation $q a - R b = 1$ in $\mathbb{Z}$. Thus the hypotheses guarantee that the complementary divisor $R = M/q$ exists as a natural number and is coprime to $q$, so that $1$ is an integral linear combination of $q$ and $R$ of the stated shape. The conclusion is mere nonemptiness of the structure, not a choice of canonical datum; in particular no normalisation of $a$ and $b$ (such as size or congruence conditions) is asserted.
--
--   The structure packages the data underlying the Atkin–Lehner involution $W_q$ at a prime exactly dividing the level, whose matrix $\begin{pmatrix} qa & b \\ qR & q\end{pmatrix}$ has determinant $q$ precisely because of the relation $qa - Rb = 1$; the hypothesis $q^2 \nmid M$ is what makes such a datum exist. It is invoked wherever an Atkin–Lehner operator at such a prime is needed, in particular in the treatment of the coefficient $a_q$ of a newform at a prime exactly dividing the level and in the associated level-lowering and congruence arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd {M q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) (hsq : ¬ q ^ 2 ∣ M) :
    Nonempty (ModularForm.AtkinLehnerDatum M q) := by sorry
