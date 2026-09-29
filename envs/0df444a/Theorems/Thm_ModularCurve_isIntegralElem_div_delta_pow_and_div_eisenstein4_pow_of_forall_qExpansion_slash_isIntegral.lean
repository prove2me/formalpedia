-- Prove2me | Theorems.Thm_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
-- name    : ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/bd29f321-9110-5074-9ebb-034f8af2ae7c
-- title:
--   Integrality of g¹²/Δ^k over ℤ[j] and ℤ[j⁻¹]
-- statement:
--   Let $M$ be a nonzero natural number, $k$ a natural number, and let $g$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $p_g \in \mathbb{Z}[[X]]$ be a power series with integer coefficients whose image in $\mathbb{C}[[X]]$ equals the $q$-expansion of $g$ of width $1$. Assume that for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ and every $n$, the $n$-th coefficient of the width-$M$ $q$-expansion of $g \mid_k \gamma$ is integral over $\mathbb{Z}$, i.e. an algebraic integer. Write $\Delta_q = X\prod_{n\ge 1}(1-X^n)^{24}$ and $E_4 = 1 + 240\sum_{n\ge 1}\big(\sum_{d \mid n} d^3\big)X^n$ in $\mathbb{Z}[[X]]$, and let $j = X^{-1}\cdot \overline{jNum}$ be the Laurent series over $\mathbb{Q}$ obtained from the numerator series `jNum`. Then, in the field $\mathbb{Q}((X))$ of Laurent series, the quotient $p_g^{12}/\Delta_q^{\,k}$ is a root of a monic polynomial with coefficients in the image of $\mathbb{Z}[T] \to \mathbb{Q}((X))$, $T \mapsto j$, and the quotient $p_g^{12}/E_4^{\,3k}$ is a root of a monic polynomial with coefficients in the image of $\mathbb{Z}[T] \to \mathbb{Q}((X))$, $T \mapsto j^{-1}$; all series are mapped to $\mathbb{Q}$ coefficientwise.
--
--   This is the integrality statement underlying the construction of an affine model over $\mathbb{Z}$ for a modular curve from a modular form with algebraic-integer expansions at every cusp: the $12$-th power of the form, divided by the corresponding power of $\Delta$ (respectively of $E_4^3$), is integral over $\mathbb{Z}[j]$ (respectively $\mathbb{Z}[j^{-1}]$), the two charts of the $j$-line. It is used in the construction of integral bases of forms of full level, via [`ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit`](thm.html#ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
    (M : ℕ) [NeZero M] (k : ℕ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (pg : PowerSeries ℤ) (hg : ModularCurve.IsIntegralQExp g pg)
    (hint : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
      ((UpperHalfPlane.qExpansion (M : ℝ) ((⇑g : UpperHalfPlane → ℂ) ∣[(k : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n)) :
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) /
        ModularCurve.intSeriesC ℚ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k)) ∧
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq⁻¹).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) / ModularCurve.intSeriesC ℚ (ModularCurve.eisenstein4 ^ (3 * k))) := by sorry
