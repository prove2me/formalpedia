-- Prove2me | Theorems.Thm_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
-- name    : LanglandsTunnell.integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/7ea52320-0748-54ec-8c4b-e74d57618a1b
-- title:
--   n-fold integration by parts against a Gaussian on a half-line
-- statement:
--   Let $n$ be a natural number, $a$ a complex number with $\operatorname{Re} a > n-1$, $w$ a real number with $w > 0$, and $v$ an arbitrary real number. Write $G(s) = e^{-\pi s^2}$, regarded as a complex-valued function of the real variable $s$, and let $G^{(n)} =$ `iteratedDeriv n` $G$ be its $n$-th iterated derivative in the real variable. The assertion is the equality of Bochner integrals over the open half-line $(v/w, \infty)$ with respect to Lebesgue measure $$\int_{v/w}^{\infty} (\sigma w - v)^{a}\, G^{(n)}(\sigma)\, d\sigma \;=\; (-w)^{n} \Big(\prod_{k=0}^{n-1} (a - k)\Big) \int_{v/w}^{\infty} (\sigma w - v)^{a-n}\, e^{-\pi \sigma^{2}}\, d\sigma,$$ where in both integrands the base $\sigma w - v$ is the real number, coerced to $\mathbb{C}$, and the power is the complex power on $\mathbb{C}$ (on the domain of integration $\sigma w - v > 0$, so this is the principal power of a positive real). The product over `Finset.range n` is empty for $n = 0$, in which case the identity is trivial; the factors $(-w)^n$ and $(a-n)$ in the exponent use the coercions of $w$ and $n$ to $\mathbb{C}$.
--
--   This is the classical $n$-fold integration by parts that moves all derivatives off the Gaussian and onto the power factor, the boundary terms vanishing at $\sigma = v/w$ because $\operatorname{Re}(a-k) > 0$ for $k < n$ and at infinity by Gaussian decay. It is used in the evaluation of the fibre integrals occurring in the Langlands–Tunnell part of the development, where it feeds [`LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous`](thm.html#LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp.lean

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
    (n : ℕ) (a : ℂ) (ha : (n : ℝ) - 1 < a.re) (w : ℝ) (hw : 0 < w) (v : ℝ) :
    ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ a) *
        iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ
      = (-(w : ℂ)) ^ n * (∏ k ∈ Finset.range n, (a - (k : ℂ))) *
          ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ (a - (n : ℂ))) *
            (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) := by sorry
