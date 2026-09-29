-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime
-- name    : Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/1c2920c0-af5e-5f29-b673-545b9600f90a
-- title:
--   Trivial Schur multiplier of SL₂(𝔽_q), q≥ 5
-- statement:
--   Let $q$ be a prime with $5 \le q$. The assertion is that the group $SL(2, \mathbb{Z}/q)$, i.e. `Matrix.SpecialLinearGroup (Fin 2) (ZMod q)`, satisfies the predicate [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11): for every group $E$ (in the same universe) and every group homomorphism $\pi : E \to SL(2,\mathbb{Z}/q)$ such that $\pi$ is surjective, the kernel of $\pi$ is contained in the centre of $E$, and the kernel of $\pi$ is contained in the commutator subgroup $[E,E]$ of $E$, the kernel of $\pi$ is the trivial subgroup. In other words, every central extension $1 \to \ker \pi \to E \to SL(2,\mathbb{Z}/q) \to 1$ whose kernel lies in the derived subgroup of $E$ — a stem extension — is an isomorphism, so $SL_2(\mathbb{F}_q)$ admits no non-trivial stem extension for $q \ge 5$. No restriction beyond primality and $q \ge 5$ is imposed; the classical statement holds already for $q \ge 4$, so the form stated here is the slightly weaker one adapted to the use made of it.
--
--   This is Steinberg's theorem for $SL_2$ over a finite field: for $q \ge 4$ the group $SL_2(\mathbb{F}_q)$ is its own universal central extension, equivalently $H_2(SL_2(\mathbb{F}_q),\mathbb{Z}) = 0$. It enters the level-raising and Taylor–Wiles part of the argument, where it is used to rule out non-trivial central extensions arising from lifts of residual representations with image containing $SL_2(\mathbb{F}_q)$; the proof proceeds via [`Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem`](thm.html#Ihara.exists_pow_prime_pow_eq_one_of_sl2_stem), which bounds elements of the kernel of a stem extension by $q$-power torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime
    {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod q)) := by sorry
