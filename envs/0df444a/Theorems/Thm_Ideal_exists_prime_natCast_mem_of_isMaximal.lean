-- Prove2me | Theorems.Thm_Ideal_exists_prime_natCast_mem_of_isMaximal
-- name    : Ideal.exists_prime_natCast_mem_of_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/34d64f1d-21e8-56de-a1d2-ee17e324206e
-- title:
--   A maximal ideal of a ring finite over ℤ contains a prime
-- statement:
--   Let $T$ be a commutative ring which is finitely generated as a module over $\mathbb{Z}$, and let $\mathfrak{m}$ be an ideal of $T$ which is maximal. Then there exists a natural number $p$ which is prime and whose image $p\cdot 1_T$ under the canonical ring homomorphism $\mathbb{N}\to T$ lies in $\mathfrak{m}$. Thus the residue field $T/\mathfrak{m}$ has positive characteristic, the characteristic being the prime $p$ so produced; the statement asserts only the existence of such a prime number and asserts nothing further about $T/\mathfrak{m}$ (in particular finiteness of the residue field is not part of the conclusion), and no uniqueness of $p$ is claimed, although it is of course determined by $\mathfrak{m}$.
--
--   This is the standard observation that a maximal ideal of a ring integral over $\mathbb{Z}$ has positive residue characteristic. It is used to attach a residue characteristic to a maximal ideal of a Hecke algebra, and is cited by [`CuspForm.exists_isNormalizedEigenform_ker_of_isMaximal`](thm.html#CuspForm.exists_isNormalizedEigenform_ker_of_isMaximal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_prime_natCast_mem_of_isMaximal.lean

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.Nat.Prime.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.exists_prime_natCast_mem_of_isMaximal {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔪 : Ideal T) (h𝔪 : 𝔪.IsMaximal) : ∃ p : ℕ, p.Prime ∧ (p : T) ∈ 𝔪 := by sorry
