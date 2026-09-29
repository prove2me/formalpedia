-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_mul_goodFamily
-- name    : ModularCurve.MultCovering.eq_sum_linkMatrix_mul_goodFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/de9910fe-48e9-50f5-83f1-81691b915eca
-- title:
--   Embedding basis expanded in the good family
-- statement:
--   Let $p$ be a prime and $r$ a natural number, and let $\Phi$ be a family context `FamCtx p r`; among its data is a family $t =$ `goodFamily` $\Phi$ of $r$ elements of the field $\overline{\mathbb{Q}}(X)$ realised as `modularFunctionFieldBar (1 * p)`, the intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by base change of the full modular function field of level $1\cdot p$ to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, together with the hypothesis $\Phi.\,$`t_basis` that $t$ is an embedding basis, and the further integrality and reduction conditions of the structure. Let $s$ be a further family of $r$ elements of the same field which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its $\overline{\mathbb{Q}}$-span is the Riemann–Roch space of the divisor `embDivisor (1 * p)`, namely `embDegree (1 * p)` times the cusp at infinity. Then for every index $i$, $$s_i = \sum_{j} \iota\bigl(\mathrm{linkMatrix}(\Phi, s, h_s)_{ij}\bigr)\, t_j,$$ where $\iota$ is the structure map $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}(X)$ and the $(i,j)$ entry of the link matrix is by definition the $j$-th coordinate of $s_i$ with respect to the linearly independent family $t$.
--
--   This is the change-of-basis identity between an arbitrary embedding basis of the Riemann–Roch space attached to `embDivisor (1 * p)` and the good family carried by a `FamCtx`, written in the multiplicative spelling $\iota(a)\,x$ rather than with scalar action. It is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$, where coordinates of sections must be transported between the two families in the chart comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_mul_goodFamily.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.MultCovering.eq_sum_linkMatrix_mul_goodFamily {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (linkMatrix Φ s hs i j)
      * goodFamily Φ j := by sorry
