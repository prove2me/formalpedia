-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
-- name    : Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/42323290-481f-5e07-9702-da42f4c57d5a
-- title:
--   Trivial Schur multiplier of SL₂(ℤ/qⁿ) for q≥ 5
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $n$ be a natural number with $n \neq 0$. The assertion is that the group $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$, realised as the special linear group of $2\times 2$ matrices over `ZMod (q ^ n)`, satisfies the predicate [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11): for every group $E$ and every group homomorphism $\pi \colon E \to \mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ such that $\pi$ is surjective, $\ker \pi$ is contained in the centre of $E$, and $\ker \pi$ is contained in the commutator subgroup $[E,E]$, one has $\ker \pi = 1$. In other words, every central extension of $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ whose kernel lies in the derived subgroup of the extension group — a stem extension — is already an isomorphism. The hypotheses $q \ge 5$ and $n \ne 0$ are as stated; no further structure on $E$ beyond a group structure is assumed.
--
--   This is the vanishing of the Schur multiplier $H_2(\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z}),\mathbb{Z})$ for primes $q \ge 5$, in the equivalent formulation that all stem extensions are trivial; it fails at $q = 2$, $n \ge 2$, where the multiplier of $\mathrm{SL}_2(\mathbb{Z}/4)$ is of order $2$. It is used in the treatment of Mennicke's congruence subgroup property for $\mathrm{SL}_2$ over $\mathbb{Z}$, being cited by [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor) and [`Ihara.mennickeCSP_of_prime`](thm.html#Ihara.mennickeCSP_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    {n : ℕ} (hn : n ≠ 0) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) := by sorry
