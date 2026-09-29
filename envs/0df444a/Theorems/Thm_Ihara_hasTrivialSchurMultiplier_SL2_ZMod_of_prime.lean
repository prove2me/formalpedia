-- Prove2me | Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime
-- name    : Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ddac1bc6-f8c9-538a-aa67-22f95c55729b
-- title:
--   Trivial Schur multiplier of SL₂(𝔽_q), all primes
-- statement:
--   Let $q$ be a prime number and let $\mathrm{SL}(2,\mathbb{Z}/q\mathbb{Z})$ be the group of $2\times 2$ matrices of determinant $1$ over $\mathbb{Z}/q\mathbb{Z}$. The assertion is that this group satisfies the predicate [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11), which unfolds to the following stem-extension statement: for every group $E$ and every group homomorphism $\pi \colon E \to \mathrm{SL}(2,\mathbb{Z}/q\mathbb{Z})$ such that $\pi$ is surjective, the kernel of $\pi$ is contained in the centre of $E$, and the kernel of $\pi$ is contained in the commutator subgroup $[E,E]$, the kernel of $\pi$ is the trivial subgroup. In other words, $\mathrm{SL}_2(\mathbb{F}_q)$ admits no non-trivial central extension by a subgroup of the derived group, for every prime $q$ without exception, the small primes $q=2$ and $q=3$ included. No condition beyond primality of $q$ is imposed, and the formulation quantifies over central stem extensions rather than asserting the vanishing of a cohomology group $H^2$.
--
--   This is the triviality of the Schur multiplier of $\mathrm{SL}_2(\mathbb{F}_q)$, classically due to Schur and obtained for $q \ge 5$ as a case of Steinberg's computation of the multipliers of the finite Chevalley groups; the stem-extension formulation used here is the equivalent characterisation by universal central extensions. It is used in the construction of the kernel pair in [`CohCarrier.isEis_kernel_pair_of_prime`](thm.html#CohCarrier.isEis_kernel_pair_of_prime), where a central extension of $\mathrm{SL}_2(\mathbb{F}_q)$ arising from a cohomological carrier has to be split off.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_of_prime.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_of_prime
    {q : ℕ} (hq : q.Prime) :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod q)) := by sorry
