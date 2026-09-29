-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
-- name    : LanglandsTunnell.Converse.integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/17fc3a49-5992-5fd4-bc8b-c7682159bb8e
-- title:
--   Third Gaussian moment against the character ψ(cx)
-- statement:
--   Let $c$ be a real number and let $Y$ be a nonzero real number. The assertion is an identity of absolutely convergent Lebesgue integrals over $\mathbb{R}$, with values in $\mathbb{C}$: the integral of the function sending $x \in \mathbb{R}$ to $x^3 \cdot e^{-\pi (x^2/Y^2)} \cdot \psi(cx)$, where the real cube and the real Gaussian factor are regarded as complex numbers and $\psi$ is the additive character `ArchR.psi` of $\mathbb{R}$ given by $\psi(t) = \exp(2\pi i t)$, equals $$|Y| \cdot e^{-\pi (c^2 Y^2)} \cdot i\,\bigl(c\,Y^4\,(3/(2\pi) - c^2 Y^2)\bigr),$$ the factors $|Y|$, $e^{-\pi c^2 Y^2}$ and $c Y^4 (3/(2\pi) - c^2 Y^2)$ being real numbers coerced into $\mathbb{C}$ and $i$ the imaginary unit. In particular the value of the integral is purely imaginary, and vanishes exactly when $c = 0$ or $c^2 Y^2 = 3/(2\pi)$.
--
--   This is the third moment ($j = 3$) of the scaled Gaussian $e^{-\pi x^2/Y^2}$ against the standard additive character of $\mathbb{R}$, a companion of the corresponding $j = 0, 1, 2$ evaluations. It is used in the $x$-integration step of the dual quadratic-section computation, being cited in the evaluation of the Iwasawa fibre integral for a dual torus pair against a block-quadratic harmonic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi (c : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ 3 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * ArchR.psi (c * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * Y ^ 2))) : ℂ) * (Complex.I * (((c * Y ^ 4 * (3 / (2 * Real.pi) - c ^ 2 * Y ^ 2)) : ℝ) : ℂ)) := by sorry
