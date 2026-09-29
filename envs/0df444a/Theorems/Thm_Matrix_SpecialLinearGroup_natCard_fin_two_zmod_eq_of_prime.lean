-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime
-- name    : Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/77ed1ed1-7378-53d5-8288-f743bfa46564
-- title:
--   Order of SL₂(ℤ/p) is p(p²-1)
-- statement:
--   For a natural number $p$ that is prime, the cardinality of the group $\mathrm{SL}_2(\mathbb{Z}/p\mathbb{Z})$ — in Lean, `Matrix.SpecialLinearGroup (Fin 2) (ZMod p)`, the group of $2\times 2$ matrices over the ring $\mathbb{Z}/p\mathbb{Z}$ with rows and columns indexed by `Fin 2` and determinant $1$ — equals $p\,(p^2-1)$. The cardinality is taken as `Nat.card`, so the assertion is an identity of natural numbers (finiteness being implicit in the equality with a nonzero value), and the subtraction $p^2-1$ is truncated subtraction in $\mathbb{N}$, which is harmless since $p \ge 2$. No further hypotheses are imposed: primality of $p$ is the only assumption, and it is what makes $\mathbb{Z}/p\mathbb{Z}$ a field, so that the usual count applies.
--
--   This is the classical order formula for the special linear group of rank $2$ over a prime field. It is used in the construction of auxiliary level structures for modular curves, where the order of the relevant automorphism group at level $\ell$ must be known to be $\ell(\ell^2-1)$; the present result is cited by [`ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma`](thm.html#ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_natCard_fin_two_zmod_eq_of_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.SpecialLinearGroup.natCard_fin_two_zmod_eq_of_prime (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by sorry
