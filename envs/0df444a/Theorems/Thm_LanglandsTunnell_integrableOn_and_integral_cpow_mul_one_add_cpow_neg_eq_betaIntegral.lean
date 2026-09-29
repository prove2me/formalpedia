-- Prove2me | Theorems.Thm_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
-- name    : LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/9287eb71-a21b-5a8f-8d81-3f39e017d257
-- title:
--   Second-kind beta integral on (0,∞) equals B(b,a)
-- statement:
--   Let $a,b$ be complex numbers with $\operatorname{Re} a > 0$ and $\operatorname{Re} b > 0$. Consider the function of a real variable $q \mapsto q^{b-1}(1+q)^{-(a+b)}$, where $q$ and $1+q$ are coerced to $\mathbb{C}$ and the powers are complex `cpow` powers. The theorem asserts a conjunction: first, that this function is integrable on the ray $(0,\infty)$ with respect to Lebesgue measure (`IntegrableOn … (Set.Ioi 0)`); and second, that its integral over $(0,\infty)$ equals `Complex.betaIntegral b a`, that is, the Mathlib beta integral $\int_0^1 x^{b-1}(1-x)^{a-1}\,dx$ taken as an interval integral over $[0,1]$. Note the order of the arguments: the exponent $b-1$ of $q$ on the ray matches the exponent $b-1$ of $x$ on $(0,1)$, so the right-hand side is `betaIntegral b a` and not `betaIntegral a b` (the two agree by the symmetry of the beta function, which is not invoked in the statement).
--
--   This is the beta integral of the second kind, $\int_0^\infty q^{b-1}(1+q)^{-(a+b)}\,dq = B(b,a) = \Gamma(a)\Gamma(b)/\Gamma(a+b)$, a form not present in Mathlib, which carries only the integral over $(0,1)$. It is used in the archimedean computation of the Mellin transform appearing in [`LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div`](thm.html#LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b))) (Set.Ioi (0 : ℝ)) ∧
      ∫ q in Set.Ioi (0 : ℝ), (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b)) = Complex.betaIntegral b a := by sorry
