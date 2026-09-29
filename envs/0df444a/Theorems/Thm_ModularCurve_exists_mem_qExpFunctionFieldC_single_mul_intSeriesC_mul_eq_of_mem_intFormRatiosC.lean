-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
-- name    : ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a893ba75-827f-5f79-86f8-d541b2227ef9
-- title:
--   Integral form ratios are quotients of shifted integral q-expansions
-- statement:
--   Let $K$ be a field, let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ whose image in $\mathrm{GL}_2(\mathbb{R})$ has $1$ among its `strictPeriods`, and let $r$ be a Laurent series over $K$ lying in [`ModularCurve.intFormRatiosC K Γ`](def/ModularCurve_X1.html#L83); that is, there are an integer $k$, modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, and power series $p_f,p_g\in\mathbb{Z}[[q]]$ whose images under $\mathbb{Z}\to\mathbb{C}$ are the $q$-expansions of $f$ and of $g$ at width $1$, such that the Laurent series `intSeriesC K` $p_g$ obtained from $p_g$ by coefficientwise reduction along $\mathbb{Z}\to K$ is nonzero and $r$ is the quotient of `intSeriesC K` $p_f$ by it. The conclusion asserts the existence of Laurent series $a,b$ over $K$, integers $m,n$, and power series $P,Q\in\mathbb{Z}[[q]]$ such that $a$ and $b$ both lie in [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101), the intermediate field of $K((q))$ generated over $K$ by [`ModularCurve.intFormRatiosC K Γ`](def/ModularCurve_X1.html#L83), with $a=q^{m}\cdot$ `intSeriesC K` $P$ and $b=q^{n}\cdot$ `intSeriesC K` $Q$ (the factors $q^m$, $q^n$ being the Hahn series `HahnSeries.single m 1`, `HahnSeries.single n 1`), and moreover $b\neq 0$ and $r\,b=a$.
--
--   This is the passage from ratios of integral $q$-expansions of modular forms of equal weight to quotients of elements of the $q$-expansion function field that are themselves monomial shifts of integral power series; the mechanism is multiplication by suitable powers of the discriminant expansion, whose expansion is $q$ times a unit of $\mathbb{Z}[[q]]$ by [`ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`](thm.html#ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit). It feeds the construction of Gauss-type fractional forms in a base change of [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) and the induction expressing integral elements of the function field as quotients of integral expansions of functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
    (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (r : LaurentSeries K) (hr : r ∈ ModularCurve.intFormRatiosC K Γ) :
    ∃ (a b : LaurentSeries K) (m n : ℤ) (P Q : PowerSeries ℤ),
      a ∈ ModularCurve.qExpFunctionFieldC K Γ ∧ b ∈ ModularCurve.qExpFunctionFieldC K Γ ∧
      a = HahnSeries.single m 1 * ModularCurve.intSeriesC K P ∧
      b = HahnSeries.single n 1 * ModularCurve.intSeriesC K Q ∧
      b ≠ 0 ∧ r * b = a := by sorry
