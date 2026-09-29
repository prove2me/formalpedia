-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_colHarmonic
-- name    : LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_colHarmonic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3a6a6b60-8c4a-53fd-92e4-8fa3931837da
-- title:
--   Iwasawa fibre of a dual torus pair as quadruple integral
-- statement:
--   Fix a real archimedean parameter $P_2$ (principal with exponents and parities $(u_1,a_1,u_2,a_2)$, or discrete of weight $k\ge 1$), an archimedean datum $D$ of type `ArchDatumR P₂` — a function $D.W$ on real $2\times2$ matrices satisfying the unipotent law with additive character `ArchR.psi` $x\mapsto e^{2\pi i x}$, the central law with `ArchR.centralChar P₂`, together with the zeta-integral, functional-equation and decay axioms — an arbitrary function $W:\mathbb R\to\mathbb C$, reals $a$, $a_1\ne 0$, $a_2>0$, complex parameters $u_0$, $c_P$, $s$, parities $a_0,s_P\in\mathbb Z/2$, an integer $k$, a natural number $n$, and $\delta$ with $\delta=0$ or $\delta=1$. Here `ArchR.quasiChar u a y` $=|y|^u$ times $\operatorname{sign}(y)$ when $a\ne 0$ and $1$ when $a=0$, and `ArchR.diagOne y` $=\mathrm{diag}(y,1)$. The assertion is an equality of complex numbers: the product of $|a_1a_2|$, $i^{k}$, $|{-a_1^{-1}}|^{c_P+1}$, $((-a_1^{-1})/|{-a_1^{-1}}|)^{s_P}$, $W(-a_1/a_2)$, `ArchR.quasiChar (u₀+1) a₀ (-(a₁a₂)⁻¹)`, $2\pi$, the iterated integral over $y_1\in\mathbb R$, $y_2>0$, $x\in\mathbb R$ of the displayed Gaussian–Whittaker integrand (Gaussian factors in $a_2^{-1}x/y_1$, $a_2^{-1}/y_2$, $1/y_1$ and $aa_1y_2$, the section factor $a_1^2|y_1y_2|\,y_1^{-n}(-i\,a a_1a_2^{-1}xy_2/y_1)^{\delta}$, the quasi-character and central-character factors, $e^{2\pi i a x}$, $D.W(\mathrm{diag}(ay_1/y_2,1))$ and $y_2^2|y_1y_2|^{-4}$), $|a_1a_2|^{s-1/2}$ and $a_1^{-2}$, equals $2\pi\,i^{k}a_2^{-1}$ times the iterated integral over $q\in\mathbb R$, $p>0$ of $a_2^{2s-c_P-P_2.\mathrm{centralExponent}+n}e^{-\pi a_2^2q^2}$ times the product of sign characters in $\pm a_1/a_2$ and $q$ attached to $s_P$, $a_0$ and $n$, $W(-(a_1/a_2))$, the bracket $(p\,\mathrm{sgn}(a_1/a_2))\bigl(a^2\,\mathrm{sgn}(a_1/a_2)(pq)^{-1}\bigr)^{\delta}$, $D.W(\mathrm{diag}(a|a_1/a_2|p/q,1))$, the powers $|a_1/a_2|^{s-5/2-c_P-P_2.\mathrm{centralExponent}}|q|^{u_0+n}p^{u_0-P_2.\mathrm{centralExponent}-3}$, and $e^{-\pi(a_1/a_2)^2p^2-\pi a^2/p^2-\pi a^2/q^2}$.
--
--   This is the pointwise, fixed-$(a_1,a_2)$ fibre of the Iwasawa-unfolded dual torus pair for the weight-zero section $\det^{\delta}\cdot(\text{column harmonic})^{n}\cdot(\text{Gaussian})$, rewriting the three-variable Iwasawa integral as the four-variable torus integrand evaluated at $(a_2,a_1/a_2,q,p)$; no integrability hypothesis enters. The inner $x$-integration is the Gaussian moment of order $\delta\le 1$ supplied by [`LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv`](thm.html#LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv), and the identity feeds the integrated form [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_detPow_colHarmonic_of_re_gt) used in the archimedean analysis for the converse theorem behind Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_colHarmonic.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_colHarmonic
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) :
    (((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (k : ℤ) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) *
                      W (-a₁ / a₂))) *
                  (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
                    (((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((x * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂)) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 (a₁ / a₂) * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by sorry
