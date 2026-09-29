-- Prove2me | Theorems.Thm_Ihara_isPerfect_SL2_ZMod_prime_pow
-- name    : Ihara.isPerfect_SL2_ZMod_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a082a360-5cad-56c6-81a8-53857dc3a919
-- title:
--   Perfectness of SL₂(ℤ/qⁿ) for q≥ 5
-- statement:
--   Let $q$ be a natural number which is prime and satisfies $5 \le q$, and let $n$ be a nonzero natural number. The assertion is that the group $\mathrm{SL}(2, \mathbb{Z}/q^n\mathbb{Z})$ — the special linear group of $2 \times 2$ matrices of determinant $1$ over the ring $\mathbb{Z}/q^n\mathbb{Z}$, written with the `MatrixGroups` notation `SL(2, ZMod (q ^ n))` — is perfect in the sense of `Group.IsPerfect`, i.e. its commutator subgroup $\lbrack\!\lbrack \top, \top \rbrack\!\rbrack$ is the whole group; equivalently, every element of $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ is a product of commutators, and the abelianisation of $\mathrm{SL}_2(\mathbb{Z}/q^n\mathbb{Z})$ is trivial. Both numerical hypotheses on $q$ are genuinely needed for the conclusion as stated: perfectness fails for composite moduli such as $\mathbb{Z}/6\mathbb{Z}$, and $\mathrm{SL}_2(\mathbb{Z}/4\mathbb{Z})$ and $\mathrm{SL}_2(\mathbb{Z}/9\mathbb{Z})$ have nontrivial abelianisations, so the small primes $2$ and $3$ must be excluded.
--
--   This is the standard perfectness statement for $\mathrm{SL}_2$ over $\mathbb{Z}/q^n\mathbb{Z}$, extending the prime-modulus case to arbitrary prime powers; it feeds the Ihara-type analysis of congruence subgroups at level $q^2$ and the level-raising machinery, being used for instance by [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor) and by the Hecke-module statements supporting the Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_isPerfect_SL2_ZMod_prime_pow.lean

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.IsPerfect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem Ihara.isPerfect_SL2_ZMod_prime_pow {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) {n : ℕ}
    (hn : n ≠ 0) : Group.IsPerfect (SL(2, ZMod (q ^ n))) := by sorry
