-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_goodFamilyZero_mem_zeroChart_integers
-- name    : ModularCurve.MultCovering.FamData.goodFamilyZero_mem_zeroChart_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6bdcbd7b-d3d1-59d5-8a78-24a43598a65f
-- title:
--   ̄ 0-chart integrality of a 0-orthogonal family
-- statement:
--   Let $p$ be a prime and $r$ a natural number, and let $D$ be family data of level $1\cdot p$: a family $t_l \in \overline{\mathbb{Q}}\cdot(\text{modular function field of level } 1\cdot p)$, $l \in \mathrm{Fin}\,r$, together with rational representatives $t^{\mathrm{rat}}_l$ in the rational modular function field $\mathbb{Q}(\text{divisor expansions})\subseteq \mathbb{Q}((q))$ such that each $t_l$ is the coefficientwise image of $t^{\mathrm{rat}}_l$ in the base change to $\overline{\mathbb{Q}}$. Assume `hbasis`, that $(t_l)_l$ is linearly independent over $\overline{\mathbb{Q}}$ and spans the Riemann–Roch space of the divisor `embDivisor (1 * p)`, i.e. is a basis of that space. Assume the orthogonality hypothesis `horthZero`: for every $c \in \mathbb{Q}^r$, all Laurent coefficients of $\sum_i c_i\,w(t^{\mathrm{rat}}_i)$ have non-negative $p$-adic valuation if and only if $v_p(c_i) \ge -n_i$ for all $i$, where $w$ denotes `frickeInvolutionFull (1 * p)` (a chosen Fricke automorphism of the rational modular function field of level $1\cdot p$ when one exists, the identity otherwise) and $n_i =$ `hasseExp D i`, the Hasse content of $D$ at $i$ truncated to $\mathbb{N}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and residue field of characteristic $p$, and let $\Gamma$ be a chart context over $(p, A)$. Then for every $l$ the rescaled member $p^{-n_l}t_l$ lies in the integers of the component chart `zeroChart Γ`, the pullback of `infChart Γ` along `frickeInvolutionBar (1 * p)`; equivalently, $w(p^{-n_l}t_l)$ lies in the integers of `infChart Γ`.
--
--   This is the $\bar 0$-cusp integrality half of the two-chart analysis of the multiplicative covering of $X_0(p)$, stated over bare family data together with the orthogonality condition at the cusp $0$ rather than over an assembled good-family context. It is used by [`ModularCurve.MultCovering.FamData.t_zeroChart_of_orth`](thm.html#ModularCurve.MultCovering.FamData.t_zeroChart_of_orth) and by the existence theorem [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue), which produces a family whose rescaled members are integral on both charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_goodFamilyZero_mem_zeroChart_integers.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.goodFamilyZero_mem_zeroChart_integers (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r) (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers := by sorry
