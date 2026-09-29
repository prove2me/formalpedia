-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
-- name    : ModularCurve.MultCovering.linkMatrixInv_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/e631ceca-2282-5148-a981-277aca755736
-- title:
--   Left inverse property of the link matrix
-- statement:
--   Let $p$ be a prime and $r$ a natural number. Let $\Phi$ be a family context `FamCtx p r` for the prime-level covering; among its data is a family $t = (t_l)_{l<r}$ of elements of $\overline{L} :=$ `modularFunctionFieldBar (1 * p)` (the base change to $\overline{\mathbb{Q}}$, inside Laurent series over $\overline{\mathbb{Q}}$, of the full modular function field of level $1\cdot p$) together with the hypothesis `t_basis`, namely `IsEmbBasis (1 * p) t`. Let $s = (s_i)_{i<r}$ be a further family in $\overline{L}$ satisfying `IsEmbBasis (1 * p) s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space of the divisor `embDivisor (1 * p)`, the multiple of the cusp at infinity with multiplicity `embDegree (1 * p)`; the same two conditions hold for $t$. The matrix `linkMatrix Φ s hs` has $(i,j)$ entry the $j$-th coordinate of $s_i$ with respect to the linearly independent family $t$, and `linkMatrixInv Φ s hs` has $(i,j)$ entry the $j$-th coordinate of $t_i$ with respect to $s$. The assertion is the identity $\mathrm{linkMatrixInv} \cdot \mathrm{linkMatrix} = 1$ in the ring of $r \times r$ matrices over $\overline{\mathbb{Q}}$.
--
--   This is the change-of-basis compatibility between an embedding basis $s$ of the relevant Riemann–Roch space and the good family $t$ carried by the family context: the two coordinate matrices are mutually inverse, here in the form that the inverse link matrix is a left inverse. It is used in the comparison of coordinates across the charts at the cusps $\infty$ and $0$ of the prime-level covering, and in the resulting proximity estimates for evaluation vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_linkMatrixInv_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.linkMatrixInv_mul {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    linkMatrixInv Φ s hs * linkMatrix Φ s hs = 1 := by sorry
