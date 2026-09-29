-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_linkBudget
-- name    : ModularCurve.MultCovering.exists_linkBudget
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/1cf398d5-8ea3-5c6c-ad2d-bd020d88b994
-- title:
--   A uniform p-power budget for the link matrices
-- statement:
--   Let $p$ be a prime (as a natural number carrying a primality instance), let $r$ be a natural number, and let $\Phi$ be a family context `FamCtx p r` for the covering of level $1\cdot p$; among its data is a family $t : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}$-points of `modularFunctionFieldBar (1 * p)` satisfying `IsEmbBasis (1 * p)`, together with the reduction conditions at the infinity and zero charts recorded in that structure. Let $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar (1 * p)` be a further family, and assume `IsEmbBasis (1 * p) s`, that is: $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its range spans the Riemann–Roch space of the divisor `embDivisor (1 * p)`, the multiple `embDegree (1 * p)` of the cusp at infinity. The assertion is that there exists a natural number $B$ such that for every valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, i.e. with the image of $p$ a nonunit of $A$, and for all indices $i, j$, both $p^{B}\cdot(\mathrm{linkMatrix}\,\Phi\,s\,hs)_{ij}$ and $p^{B}\cdot(\mathrm{linkMatrixInv}\,\Phi\,s\,hs)_{ij}$ lie in $A$; here the first matrix records the coordinates of $s\,i$ in the basis $t$ of $\Phi$ and the second the coordinates of $t\,i$ in the basis $s$. The single exponent $B$ is uniform in $A$, $i$ and $j$.
--
--   The two link matrices are the mutually inverse change-of-basis matrices between the distinguished family $t$ of the covering family context and an arbitrary embedding basis $s$ of the same Riemann–Roch space; this statement says that a single power of $p$ clears denominators of all their entries simultaneously, at every valuation subring of $\overline{\mathbb{Q}}$ over $p$. It provides the nonemptiness needed to define the numerical invariant used in [`ModularCurve.MultCovering.linkBudget_spec`](thm.html#ModularCurve.MultCovering.linkBudget_spec), where such a bound is fixed once and for all.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_linkBudget.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_linkBudget {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ i j, (p : AlgebraicClosure ℚ) ^ B * linkMatrix Φ s hs i j ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ B * linkMatrixInv Φ s hs i j ∈ A := by sorry
