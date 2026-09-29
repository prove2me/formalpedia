-- Prove2me | Theorems.Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
-- name    : IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/ddeb62b1-4c63-586a-b968-5f6871147b8e
-- title:
--   Height-one primes are principal in regular local rings of dimension ≤ 2
-- statement:
--   Let $R$ be a commutative ring that is a regular local ring, and assume its Krull dimension satisfies $\operatorname{ringKrullDim} R \le 2$ (the inequality being taken in the extended value type in which `ringKrullDim` lands, so that in particular $R$ is allowed to have dimension $0$, $1$ or $2$). Let $P$ be an ideal of $R$ which is prime and whose height, in the sense of `Ideal.height`, equals $1$. The conclusion is that $P$ is principal as an $R$-submodule of $R$, i.e. there is an element $p \in R$ with $P = (p) = R\cdot p$. No hypothesis beyond regularity, the dimension bound, primality and the height condition is imposed; the statement is the local, dimension-$\le 2$ form of the assertion that height-one primes of a regular local ring are principal, not the general Auslander–Buchsbaum theorem.
--
--   This is the operational, stalkwise form of the statement that a regular ring of dimension at most two is factorial in the relevant local sense: height-one primes in such a local ring are principal. It is used where line bundles trivial on a generic fibre are described by vertical divisors, notably in the invertibility of vanishing ideal sheaves on regular two-dimensional schemes and in the divisor computations on integral models of modular curves that depend on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (P : Ideal R) (hP : P.IsPrime) (hP1 : P.height = 1) :
    Submodule.IsPrincipal P := by sorry
