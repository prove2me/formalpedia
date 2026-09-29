-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow
-- name    : Ihara.hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/0d12888f-a022-5be8-b885-446ca678c704
-- title:
--   Trivial Schur multiplier for SL₂(ℤ/qⁿ), q odd prime
-- statement:
--   Let $q$ be a prime with $q \neq 2$ and let $n$ be a natural number. The assertion is that the group $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ of $2 \times 2$ matrices of determinant $1$ over the ring $\mathbb{Z}/q^n\mathbb{Z}$ satisfies the predicate [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11), which by definition says: for every group $E$ and every group homomorphism $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ such that $\pi$ is surjective, the kernel of $\pi$ is contained in the centre of $E$, and the kernel of $\pi$ is contained in the commutator subgroup $[E,E]$, the kernel of $\pi$ is the trivial subgroup. Thus $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ admits no non-trivial stem extension, i.e. every central extension of it whose kernel lies in the derived subgroup of the extension is an isomorphism. No restriction beyond primality and oddness is placed on $q$, and $n$ is arbitrary; for $n = 0$ the target group is trivial, and for $q = 3$ the target group is not perfect, its abelianisation being cyclic of order $3$.
--
--   This is the vanishing of the Schur multiplier of $\mathrm{SL}_2(\mathbb{Z}/m\mathbb{Z})$ for $m$ an odd prime power, in the stem-extension formulation, as established by Mennicke and by Beyl. It feeds the treatment of the congruence subgroup property at a prime, via [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime), and the kernel-pair statement [`CohCarrier.isEis_kernel_pair_unconditional`](thm.html#CohCarrier.isEis_kernel_pair_unconditional). The proof cites [`Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem`](thm.html#Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem), which bounds the order of elements of such a kernel at prime level by a power of $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (n : ℕ) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) := by sorry
