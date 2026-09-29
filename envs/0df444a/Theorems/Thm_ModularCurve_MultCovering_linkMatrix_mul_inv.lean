-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
-- name    : ModularCurve.MultCovering.linkMatrix_mul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/d875e386-3f30-53ed-82e2-c53bb161ca8a
-- title:
--   Link matrices satisfy M· M⁻¹=1
-- statement:
--   Let $p$ be a prime and $r$ a natural number, and let $\Phi$ be a family context `FamCtx p r`; among its data is a family $t : \mathrm{Fin}\,r \to \overline{\mathcal F}_{1\cdot p}$ in the field `modularFunctionFieldBar (1 * p)` (the base change to $\overline{\mathbb Q}$, inside Laurent series over $\overline{\mathbb Q}$, of the full modular function field of level $1\cdot p$) together with the hypothesis `t_basis` that $t$ satisfies `IsEmbBasis (1 * p)`, i.e. $t$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space of the divisor `embDivisor (1 * p)` $=$ `embDegree (1 * p)` times the cusp at infinity. Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}_{1\cdot p}$ be a further family with `hs : IsEmbBasis (1 * p) s`, so $s$ is likewise linearly independent with range spanning that same Riemann–Roch space. The conclusion is the identity of $r \times r$ matrices over $\overline{\mathbb Q}$
--   $$\mathrm{linkMatrix}\,\Phi\,s\,hs \cdot \mathrm{linkMatrixInv}\,\Phi\,s\,hs = 1,$$
--   where the $(i,j)$ entry of `linkMatrix` is the $j$-th coordinate of $s_i$ in the linearly independent family $t$, and the $(i,j)$ entry of `linkMatrixInv` is the $j$-th coordinate of $t_i$ in the family $s$.
--
--   This is the change-of-basis statement that the two link matrices relating the distinguished family $t$ of the prime-level covering family context to an arbitrary embedding basis $s$ of the same Riemann–Roch space are mutually inverse, in the order $M\cdot M^{-1}=1$. It is used in the comparison of coordinates between charts at the cusp at infinity and at the zero cusp, and in the resulting estimates on evaluation vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_linkMatrix_mul_inv.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.linkMatrix_mul_inv {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    linkMatrix Φ s hs * linkMatrixInv Φ s hs = 1 := by sorry
