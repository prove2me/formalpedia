-- Prove2me | Theorems.Thm_ModularCurve_towerInclBar_finiteAlong
-- name    : ModularCurve.towerInclBar_finiteAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/c391afd9-fa52-529d-a55c-89093b46d762
-- title:
--   Finiteness of the modular function field tower along N ∣ M
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ and $M$ be natural numbers, each nonzero, and let $h$ be a proof that $N$ divides $M$. For a level $K$, `modularFunctionFieldFull K` denotes the intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the family `divisorExpansions K`, and for an intermediate field $F_0 \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ the base change `laurentBaseChange L F₀` is the intermediate field of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the image of $F_0$ under the coefficientwise embedding `coeffEmb L`. The map `towerInclBar L h` is the $L$-algebra inclusion of `laurentBaseChange L (modularFunctionFieldFull N)` into `laurentBaseChange L (modularFunctionFieldFull M)` provided by the containment of these two intermediate fields. The assertion is `FiniteAlong L (towerInclBar L h)`: regarding the larger field as an algebra over the smaller one via this inclusion, it is a finite module, i.e. the field extension $L\cdot F_N^{\mathrm{full}} \subseteq L\cdot F_M^{\mathrm{full}}$ is finite.
--
--   This is the finiteness of the degeneracy tower of base-changed modular function fields, the function-field counterpart of finiteness of the map $X(M) \to X(N)$ for $N \mid M$. It supplies the finiteness hypothesis needed to form norms and degrees along the tower, and is used in the divisor-theoretic identities for the Hecke correspondences, among them [`ModularCurve.heckeDivBar_cuspidalDivisor_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_of_prime) and the relations expressing `heckeDivBar` together with the Atkin–Lehner and Fricke involutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_towerInclBar_finiteAlong.lean

import Definitions.Def_ModularCurve_DegeneracyTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.towerInclBar_finiteAlong (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) : FiniteAlong L (towerInclBar L h) := by sorry
