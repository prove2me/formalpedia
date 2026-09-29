-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnramifiedAt_residual
-- name    : GaloisRepAdic.isUnramifiedAt_residual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ef43c02e-9a7f-5882-8944-b13ff5076fce
-- title:
--   Unramifiedness passes to the residual representation
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an adic Galois representation over $A$ in the sense of the project: a free finite $A$-module $V$ with $\operatorname{rank}_A V = 2$, a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to the $A$-linear endomorphisms of $V$, together with the adic continuity condition that for every $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho.\rho\,\sigma\,v - v \in \mathfrak{m}_A^n\cdot V$ for all $v \in V$. Let $q$ be a natural number and assume that $\rho$ is unramified at $q$ in the stated sense: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ lying in the nonunits of $P$, and every $\sigma$ in the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ over $\mathbb{Q}$, one has $\rho.\rho\,\sigma = 1$. Then the residual representation of $\rho$, namely the $\operatorname{ResidueField} A$-representation on $\operatorname{ResidueField} A \otimes_A V$ with $\sigma$ acting by the base change of $\rho.\rho\,\sigma$, is unramified at $q$ in the same sense. No primality of $q$ is assumed, and only this implication is asserted, not its converse.
--
--   This is the standard remark that the ramification set of the residual representation is contained in that of the adic representation, so that reductions of representations unramified outside a finite set $S$ are again unramified outside $S$. It is used in the comparison of level and ramification, being cited in the level-divisibility statement for newforms attached to a point of the relevant modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnramifiedAt_residual.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.isUnramifiedAt_residual {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnramifiedAt q) : ρ.residual.IsUnramifiedAt q := by sorry
