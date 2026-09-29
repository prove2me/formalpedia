-- Prove2me | Theorems.Thm_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
-- name    : ModularCurve.exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/edd220ce-1ba1-59b8-9713-3d972a8c53f4
-- title:
--   Level-one weight 12m forms: q-expansion equals P(j)Δ^m
-- statement:
--   Let $m$ be a natural number and $k$ an integer with $k = 12m$, and let $h$ be a modular form of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ given by the image of $\mathrm{SL}_2(\mathbb{Z})$ under the map `Matrix.SpecialLinearGroup.mapGL ℝ`, i.e. a level-one form. Then there exists a polynomial $P \in \mathbb{C}[X]$ whose `natDegree` is at most $m$ such that the following identity holds in the Laurent series field $\mathbb{C}((q))$ (Hahn series over $\mathbb{Z}$ with coefficients in $\mathbb{C}$): the image, under the inclusion of power series into Laurent series, of the $q$-expansion of $h$ taken with period $1$ equals $P$ evaluated at [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15) times [`ModularCurve.intSeriesC ℂ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ m)`](def/ModularCurve_X1.html#L69). Here `jqModC ℂ` is $q^{-1}$ times the image in $\mathbb{C}[[q]]$ of the integral power series `jNum` $=$ `eisenstein4`$^3 \cdot$ `dedekindEtaUnitInv`, and the second factor is the image in $\mathbb{C}[[q]]$ of $\bigl(q\prod_{n\ge 1}(1-q^{n})^{24}\bigr)^{m}$, i.e. of $\Delta^m$; thus the asserted identity reads $\hat h(q) = P(j(q))\,\Delta(q)^m$.
--
--   This is the $q$-expansion form of the classical structure theorem for level-one modular forms, $M_{12m}(\mathrm{SL}_2(\mathbb{Z})) = \Delta^m \cdot \{P(j) : \deg P \le m\}$, obtained from $E_4^3 = j\Delta$. It is used in the proofs that $h/\Delta^m$ and $h/E_4^{3m}$ are integral elements, in the form recorded by [`ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral`](thm.html#ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral) and [`ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1`](thm.html#ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_isIntegralQExp_gamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_polynomial_ofPowerSeries_qExpansion_eq_aeval_jqModC_mul_of_levelOne
    (m : ℕ) {k : ℤ} (hk : k = 12 * (m : ℤ))
    (h : ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range k) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑h : UpperHalfPlane → ℂ)) =
        Polynomial.aeval (ModularCurve.jqModC ℂ) P *
          ModularCurve.intSeriesC ℂ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ m) := by sorry
