-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq
-- name    : ModularCurve.exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/5e6b5c98-6dea-5d8d-8237-b7fb1ea0c6af
-- title:
--   Weight-k form from a square on Γ₁(M)
-- statement:
--   Fix a nonzero natural number $M$ and a natural number $k$, and let $w$ be a modular form of weight $1$ for $\Gamma_1(M)$ (regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$). Let $X$ be a Laurent series over $\mathbb{C}$ belonging to [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (Gamma1 M))`](def/ModularCurve_LaurentCoeff.html#L103), that is, to the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image under $\mathbb{Q} \to \mathbb{C}$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients `intSeriesC ℚ pf / intSeriesC ℚ pg`, where $f,g$ are modular forms of one and the same weight for $\Gamma_1(M)$, the power series $pf, pg$ over $\mathbb{Z}$ satisfy `IsIntegralQExp` for $f$ and $g$ respectively, and `intSeriesC ℚ pg ≠ 0`. Suppose further that there is a modular form $F_2$ of weight $2k$ for $\Gamma_1(M)$ whose $q$-expansion of width $1$, viewed as a Laurent series over $\mathbb{C}$, equals $\bigl(X \cdot q\text{-}\mathrm{exp}(w)^k\bigr)^2$. Then there exists a modular form $f$ of weight $k$ for $\Gamma_1(M)$ whose width-$1$ $q$-expansion, as a Laurent series, equals $X \cdot q\text{-}\mathrm{exp}(w)^k$.
--
--   This is the holomorphy criterion that a meromorphic modular object of weight $k$ on $\Gamma_1(M)$ whose square is a holomorphic form of weight $2k$ is itself holomorphic and bounded at the cusps, stated at the level of $q$-expansions; the element $X$ of the function field of $X_1(M)$, base changed to $\mathbb{C}$, is written as a ratio of forms of a common weight by [`ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC`](thm.html#ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC), and the resulting weight-$k$ form is produced by [`ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex`](thm.html#ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex). It feeds the construction of many linearly independent forms of odd weight in [`ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card_of_odd`](thm.html#ModularForm.exists_linearIndependent_gamma1_dimFormula_le_card_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_modularForm_gamma1_qExpansion_eq_mul_pow_of_qExpansion_eq_sq
    (M : ℕ) [NeZero M] (k : ℕ) (w : ModularForm (Gamma1 M) 1)
    (X : LaurentSeries ℂ)
    (hX : X ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))
    (F₂ : ModularForm (Gamma1 M) (2 * (k : ℤ)))
    (hF₂ : HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 F₂) =
      (X * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ k) ^ 2) :
    ∃ f : ModularForm (Gamma1 M) (k : ℤ),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) =
        X * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 w) ^ k := by sorry
