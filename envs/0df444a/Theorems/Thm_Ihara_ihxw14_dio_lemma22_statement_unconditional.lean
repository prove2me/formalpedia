-- Prove2me | Theorems.Thm_Ihara_ihxw14_dio_lemma22_statement_unconditional
-- name    : Ihara.ihxw14_dio_lemma22_statement_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/bc8563b3-43b5-5699-97b3-529017a6ab81
-- title:
--   Mennicke's Lemma 2.2 for SL₂(ℤ[1/q]), unconditionally
-- statement:
--   Fix a non-zero natural number $q$ with $2 \le q$, and write $\mathbb{Z}[1/q]$ for `ZAway q`, the localisation of $\mathbb{Z}$ away from $q$. The assertion is that for every natural number $m$, every proof `hmq` that $m$ and $q$ are coprime, and under the two divisibility hypotheses that $q^2 - 1$ (natural subtraction) divides $m$ and that every prime $\ell$ dividing $m$ divides $q^2 - 1$, one has $\mathtt{Ihara.mennickeZ q m hmq} = \top$, i.e. the subgroup $Z_m$ of $SL(2,\mathbb{Z}[1/q])$ is the whole group. Here $Z_m$ is, by definition, the preimage under the quotient homomorphism $SL(2,\mathbb{Z}[1/q]) \to SL(2,\mathbb{Z}[1/q])/Q_m$ of the centraliser of the image of the principal congruence subgroup of level $m$, where $Q_m = \mathtt{Ihara.mennickeQ q m}$ is the normal closure of the single element $(\mathtt{slToAway q mennickeA})^m$, the $m$-th power of the image in $SL(2,\mathbb{Z}[1/q])$ of the matrix `mennickeA`, and the principal congruence subgroup `principalCongruenceAway m q hmq` is the kernel of the reduction homomorphism `slAwayReduction m q hmq`. Equivalently: every element of $SL(2,\mathbb{Z}[1/q])$ commutes modulo $Q_m$ with every matrix congruent to the identity modulo $m$.
--
--   This is Lemma 2.2 of Mennicke's paper on Ihara's modular group, for the levels $m$ that are divisible by $q^2-1$ and supported on the primes dividing $q^2-1$; it is obtained from [`Ihara.mennickeZ_eq_top_of_corrected_reading_of_diophantine`](thm.html#Ihara.mennickeZ_eq_top_of_corrected_reading_of_diophantine) by discharging that statement's arithmetic solvability hypothesis, so that the conclusion holds with no further input. It feeds the factorisation [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor) and the congruence subgroup statement [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_ihxw14_dio_lemma22_statement_unconditional.lean

import Definitions.Def_IharaMennickeCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ihara.ihxw14_dio_lemma22_statement_unconditional (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∀ m : ℕ, ∀ hmq : Nat.Coprime m q, (q ^ 2 - 1) ∣ m →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1)) →
      Ihara.mennickeZ q m hmq = ⊤ := by sorry
