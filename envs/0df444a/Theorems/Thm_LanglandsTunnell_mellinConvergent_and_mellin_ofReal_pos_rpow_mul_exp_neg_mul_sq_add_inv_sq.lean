-- Prove2me | Theorems.Thm_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq
-- name    : LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/c7b83aaa-0909-5ad5-b9bc-e3fed17060b4
-- title:
--   Mellin transform of w^N e^-b(w²+w⁻²): convergence and positivity
-- statement:
--   Let $b$ be a real number with $b>0$ and let $N$ be an arbitrary real number. Consider the function on $(0,\infty)$ given by $w\mapsto w^{N}e^{-b(w^{2}+w^{-2})}$, where $w^N$ is the real power function and the value is regarded as a complex number via the inclusion $\mathbb{R}\hookrightarrow\mathbb{C}$. The theorem asserts two things about this function. First, for every $s\in\mathbb{C}$ the Mellin integral $\int_0^\infty w^{s-1}w^{N}e^{-b(w^{2}+w^{-2})}\,dw$ is convergent in Mathlib's sense, i.e. the integrand $w\mapsto w^{s-1}\cdot w^{N}e^{-b(w^{2}+w^{-2})}$ is integrable on $(0,\infty)$ for the Lebesgue measure; no restriction on $\operatorname{Re}(s)$ is imposed, the exponent $N$ being allowed to be negative as well. Second, for every real $x$ there exists a real number $r>0$ such that the Mellin transform of this function, evaluated at the complex point $x$, equals $r$. Thus along the real axis the Mellin transform takes values that are real and strictly positive, in particular non-zero.
--
--   This is the positivity and unrestricted convergence statement for the archimedean Mellin kernel $w^N e^{-b(w^2+w^{-2})}$, whose Mellin transform is a modified Bessel ($K$-Bessel) integral; the parameter $b>0$ is left free so that dilated Gaussian kernels $e^{-\pi(w^{-2}+a^2w^2)}$ can be rescaled to this shape. It is used in the converse-theorem and cubic-induction parts of the Langlands–Tunnell argument to produce points on the real axis where archimedean zeta integrals built from such kernels are non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.mellinConvergent_and_mellin_ofReal_pos_rpow_mul_exp_neg_mul_sq_add_inv_sq (b : ℝ) (hb : 0 < b) (N : ℝ) :
    (∀ s : ℂ, MellinConvergent (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) s) ∧
    ∀ x : ℝ, ∃ r : ℝ, 0 < r ∧
      mellin (fun w : ℝ => ((w ^ N * Real.exp (-(b * (w ^ 2 + (w ^ 2)⁻¹))) : ℝ) : ℂ)) (x : ℂ) = (r : ℂ) := by sorry
