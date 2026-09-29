-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_one_le_hasseExp_of_orth
-- name    : ModularCurve.MultCovering.FamData.one_le_hasseExp_of_orth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0b3d9e86-e635-5cfa-8dba-097415b01dc3
-- title:
--   Hasse exponent at least one for nonzero indices
-- statement:
--   Let $p$ be a prime, $r$ a natural number, and let $D$ be a `FamData p r`: a family $t_0,\dots,t_{r-1}$ of elements of the base-changed modular function field $\mathrm{modularFunctionFieldBar}(1\cdot p)$ over $\overline{\mathbb Q}$ together with elements $t^{\mathbb Q}_0,\dots,t^{\mathbb Q}_{r-1}$ of the rational modular function field $\mathrm{modularFunctionFieldFull}(1\cdot p)\subseteq \mathbb Q((q))$ such that each $t_l$ is the coefficientwise embedding of $t^{\mathbb Q}_l$. Assume: $t_l=1$ whenever the index $l$ is $0$; the family $t$ is an `IsEmbBasis` for $1\cdot p$, i.e. it is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the divisor $\mathrm{embDegree}(1\cdot p)\cdot \overline{\infty}$; orthogonality at $\infty$, namely for every $c\in\mathbb Q^r$ all Laurent coefficients of $\sum_i c_i t^{\mathbb Q}_i$ have nonnegative $p$-adic valuation if and only if $v_p(c_i)\ge 0$ for all $i$; and orthogonality at $0$, namely for every $c\in\mathbb Q^r$ all Laurent coefficients of $\sum_i c_i\,w_p(t^{\mathbb Q}_i)$, with $w_p$ the Fricke automorphism `frickeInvolutionFull`, have nonnegative $p$-adic valuation if and only if $v_p(c_i)\ge -\mathrm{hasseExp}(D,i)$ for all $i$, where $\mathrm{hasseExp}(D,i)$ is the truncation to $\mathbb N$ of $\mathrm{hasseContent}(D,i)$. Let further $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, with residue field of characteristic $p$, and let $\Gamma$ be a chart context `ChartCtx p A`. Then $\mathrm{hasseExp}(D,l)\ge 1$ for every index $l\ge 1$.
--
--   This supplies the positivity of the $0$-cusp exponents $n_l$ required when the two component charts of $X_0(p)$ over $A$ are compared, the degenerate case $n_l=0$ being excluded by the orthogonality relations at the two cusps. It is used in the construction of a family context, namely by [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_one_le_hasseExp_of_orth.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.one_le_hasseExp_of_orth (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)
    (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp D l := by sorry
