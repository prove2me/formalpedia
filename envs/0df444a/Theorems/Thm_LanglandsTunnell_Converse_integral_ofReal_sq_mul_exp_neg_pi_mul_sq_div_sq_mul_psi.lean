-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
-- name    : LanglandsTunnell.Converse.integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b47e1711-c8bf-5669-bb2e-4851a0152255
-- title:
--   Second Gaussian moment against the additive character
-- statement:
--   Let $c$ be a real number and let $Y$ be a non-zero real number. The assertion is an identity between Lebesgue integrals over $\mathbb{R}$ of complex-valued functions: the integral of $x \mapsto x^{2}\,e^{-\pi (x^{2}/Y^{2})}\,\psi(cx)$, where $x^{2}$ and the real Gaussian factor are taken with their coercions into $\mathbb{C}$ and where $\psi$ is the real additive character $\psi(t) = \exp(2\pi i t)$ of the project (so that $\psi(cx) = e^{2\pi i c x}$), equals $$|Y|\; e^{-\pi c^{2} Y^{2}}\;\Bigl(Y^{2}\bigl(\tfrac{1}{2\pi} - c^{2} Y^{2}\bigr)\Bigr),$$ the three factors on the right again being coercions of real numbers into $\mathbb{C}$. No integrability hypothesis is imposed; it is part of the content that the integral has the stated value, the only hypothesis on the parameters being $Y \neq 0$.
--
--   This is the second moment ($j = 2$) of the Gaussian against an additive character, in the rescaled form $x = |Y|u$ that occurs in the archimedean $x$-integration of the Rankin–Selberg computation for the converse theorem; it is the companion of the zeroth and first moments in that family. It is used in the evaluation of the Iwasawa-coordinate archimedean integrals of the block-quadratic harmonic integrands appearing in [`LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic`](thm.html#LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_detPow_blockQuadratic_colHarmonic) and [`LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple`](thm.html#LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_ofReal_sq_mul_exp_neg_pi_mul_sq_div_sq_mul_psi (c : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ 2 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * ArchR.psi (c * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * Y ^ 2))) : ℂ) * (((Y ^ 2 * (1 / (2 * Real.pi) - c ^ 2 * Y ^ 2) : ℝ)) : ℂ) := by sorry
