-- Prove2me | Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
-- name    : ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/2e119b14-6e6e-5370-aa0d-7d63fdd1b4e9
-- title:
--   Cusp forms of weight 2m from integrality of X over ℂ[J] and ℂ[1/J]
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, let $m\ge 1$ be a natural number and let $M$ be a natural number. Write $J$ for [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), the Laurent series $q^{-1}\cdot jNum$ over $\mathbb{C}$, where $jNum = E_4^3\cdot$ `dedekindEtaUnitInv` is the integral power series whose $q^{-1}$-shift is the $q$-expansion of $j$, and write $\vartheta$ for the $\mathbb{C}$-linear operator [`ModularCurve.thetaL ℂ`](def/ModularCurve_QExpansionDiff.html#L16) on $\mathbb{C}((q))$ sending $w$ to $\mathrm{single}(1,1)\cdot w'$, i.e. $q\,d/dq$. Let $X\in\mathbb{C}((q))$ lie in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image under $\mathbb{Q}\to\mathbb{C}$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$, where $f,g$ run over modular forms of one weight $k$ on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ with integral $q$-expansions $p_f,p_g$ in the sense of `IsIntegralQExp` and $\mathrm{intSeriesC}\,p_g\neq 0$. Assume that $X^6 J^{4m}(J-1728)^{3m}$ is integral over the $\mathbb{C}$-subalgebra $\mathbb{C}[J]$ of $\mathbb{C}((q))$, and that $X^{2M}J^{mM+1}(J-1728)^{mM}$ is integral over $\mathbb{C}[J^{-1}]$. Then there exists a cusp form $f$ of weight $2m$ on $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansion of width $1$, regarded as an element of $\mathbb{C}((q))$, equals $X\cdot(\vartheta J)^m$.
--
--   This is the analytic criterion recognising an element of the $q$-expansion function field of $X(\Gamma)$, multiplied by $(\vartheta J)^m$, as the $q$-expansion of a weight-$2m$ cusp form, the two integrality hypotheses encoding holomorphy in the interior and at the cusps respectively. It is used to convert regular differentials on the function field into weight-$2$ cusp forms and thereby to bound the genus of the relevant function field by the dimension of the space of weight-$2$ cusp forms on $\Gamma_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (m : ℕ) (hm : 1 ≤ m)
    (X : LaurentSeries ℂ)
    (hX : X ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) (M : ℕ)
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.jqModC ℂ ^ (4 * m) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.jqModC ℂ ^ (m * M + 1) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M))) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (m : ℤ)),
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) =
        X * ModularCurve.thetaL ℂ (ModularCurve.jqModC ℂ) ^ m := by sorry
