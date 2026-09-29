-- Prove2me | Theorems.Thm_Matrix_natCard_GL_fin_two_zmod_eq
-- name    : Matrix.natCard_GL_fin_two_zmod_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/88cba108-5070-50a0-a8c0-32074b25a353
-- title:
--   Order of GL₂(ℤ/p)
-- statement:
--   Let $p$ be a natural number which is prime. The assertion is that the group $\mathrm{GL}_2(\mathbb{Z}/p)$ — the general linear group of $2 \times 2$ matrices over the ring $\mathbb{Z}/p$, indexed by `Fin 2`, i.e. the unit group of the matrix ring — is finite of cardinality $(p^2 - 1)(p^2 - p)$. The cardinality is taken as `Nat.card`, which for a finite group is its order (and would be $0$ for an infinite one, so the equation also records finiteness since the right-hand side is nonzero for $p$ prime). The subtractions on the right are truncated subtraction of natural numbers, which is harmless here because $p \ge 2$ and hence $p \le p^2$ and $1 \le p^2$. No further hypotheses appear: the statement is exactly the standard count of ordered bases of a two-dimensional vector space over the field with $p$ elements.
--
--   This is the classical order formula for $\mathrm{GL}_2$ over a prime field, $|\mathrm{GL}_2(\mathbb{F}_p)| = (p^2-1)(p^2-p) = (p-1)\,|\mathrm{SL}_2(\mathbb{F}_p)|$. It is used in the analysis of full-level modular curves, where counts of minimal primes and of components are compared with the degree of level structures, the index being expressed through the order of $\mathrm{GL}_2(\mathbb{Z}/p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_natCard_GL_fin_two_zmod_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.natCard_GL_fin_two_zmod_eq (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by sorry
