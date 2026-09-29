-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_towerInclBar_of_eq
-- name    : ModularCurve.finrankAlong_towerInclBar_of_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/83eb7d69-187e-5595-86c6-7bf61ac49b8e
-- title:
--   Degree one along the equal-level tower inclusion
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $A$ and $B$ be non-zero natural numbers subject to two hypotheses: $A = B$, and $A \mid B$ (the latter is the datum needed to form the map). Write $F^{\mathrm{full}}_N$ for the intermediate field $\mathbb{Q}(\mathrm{divisorExpansions}\ N)$ of the Laurent series field $\mathbb{Q}((q))$, obtained by adjoining to $\mathbb{Q}$ the set of divisor expansions of level $N$, and write $L\cdot F^{\mathrm{full}}_N$ for `laurentBaseChange`, the subfield of $L((q))$ generated over $L$ by the image of $F^{\mathrm{full}}_N$ under the coefficientwise embedding $\mathbb{Q}((q)) \to L((q))$. Divisibility $A \mid B$ gives an inclusion $L\cdot F^{\mathrm{full}}_A \subseteq L\cdot F^{\mathrm{full}}_B$, and `towerInclBar` is the corresponding $L$-algebra map between these intermediate fields. The assertion is that the quantity [`AlgebraicCurve.finrankAlong`](def/AlgebraicCurve_Correspondence.html#L51) of this map, namely the $\mathbb{Z}$-valued rank of $L\cdot F^{\mathrm{full}}_B$ as a module over $L\cdot F^{\mathrm{full}}_A$ via the map, equals $1$; equivalently, at equal levels the inclusion is an equality of fields.
--
--   This records the degenerate case of the degeneracy-map tower: the first degeneracy inclusion between base-changed divisor-expansion fields at equal levels has degree one. It is used as a bookkeeping step in [`ModularCurve.heckeDiagonalIdentity_of_prime_of_not_dvd`](thm.html#ModularCurve.heckeDiagonalIdentity_of_prime_of_not_dvd), in the verification of the Hecke exchange square on function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_towerInclBar_of_eq.lean

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finrankAlong_towerInclBar_of_eq (L : Type*) [Field L] [Algebra ℚ L] (A B : ℕ) [NeZero A] [NeZero B] (hAB : A = B) (h : A ∣ B) : AlgebraicCurve.finrankAlong L (towerInclBar (N := A) (M := B) L h) = 1 := by sorry
