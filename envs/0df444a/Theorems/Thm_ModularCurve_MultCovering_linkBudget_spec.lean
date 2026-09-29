-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
-- name    : ModularCurve.MultCovering.linkBudget_spec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/62a3b289-b64f-5e23-b6ca-856a36db985f
-- title:
--   Link budget makes the change-of-basis matrices p-integral
-- statement:
--   Let $p$ be a prime and $r$ a natural number, and let $\Phi$ be a family context `FamCtx p r` at $p$ with $r$ members — that is, a family $t : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}(X(1\cdot p))$ of modular functions, given as `FamData`, subject to the conditions `t_basis` (the $t_l$ are linearly independent over $\overline{\mathbb{Q}}$ and span the Riemann–Roch space of the divisor $(\mathrm{embDegree}(1\cdot p))\cdot[\infty]$), `t_zero` (normalisation $t_l = 1$ for $l = 0$), and the two reduction conditions `t_inf` and `t_zeroChart` at the charts attached to any valuation subring over $p$, summarised here. Let $s : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}(X(1\cdot p))$ satisfy `IsEmbBasis (1 * p) s`, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the same Riemann–Roch space. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with `A.LiesOverPrime p`, meaning that $p$ is a non-unit of $A$. Write $M = \mathrm{linkMatrix}$ for the matrix whose $(i,j)$ entry is the $j$-th coordinate of $s_i$ in the basis $t$, and $M' = \mathrm{linkMatrixInv}$ for the matrix whose $(i,j)$ entry is the $j$-th coordinate of $t_i$ in the basis $s$. Then, with $B = \mathrm{linkBudget}\,\Phi\,s\,hs$ defined as the least natural number $B$ for which $p^{B}M_{ij}$ and $p^{B}M'_{ij}$ lie in every valuation subring of $\overline{\mathbb{Q}}$ over $p$, for all $i, j$ one has $p^{B}M_{ij} \in A$ and $p^{B}M'_{ij} \in A$.
--
--   This is the integrality statement defining the link budget: a single power of $p$ clears the denominators of the change-of-basis matrices between the normalised family $t$ of the prime-level covering and an arbitrary basis $s$ of the same Riemann–Roch space, uniformly in the valuation subring over $p$. It is the input to the change-of-coordinates comparisons at the $\infty$- and $0$-charts of the covering, and is cited by the chart-comparison and proximity estimates for the covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_linkBudget_spec.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.linkBudget_spec {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A := by sorry
