-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
-- name    : LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/da96bd26-d7d6-5902-82bf-4c66bdba8f96
-- title:
--   Non-negative log coefficients of a degree-nine Rankin–Selberg factor
-- statement:
--   Let $a,b\in\mathbb{C}$ and let $N$ be a real number with $N>1$. Assume $\lVert b\rVert=1$, that $a^2=t\,b$ for some real $t\ge 0$, and that $\lVert a\rVert^2<N+2+N^{-1}$. Then there exists a sequence of real numbers $(c_m)_{m\ge 0}$ with $c_0=0$, $c_m\ge 0$ for all $m$, and $c_m\le 9N^m$ for all $m$, such that for every $y\in\mathbb{C}$ with $\lVert y\rVert<N^{-1}$ the series $\sum_m c_m y^m$ is summable and $$\exp\Bigl(\sum_{m}c_m y^m\Bigr)=\Bigl((1-y)\,(1-ay+by^2)\,\bigl(1-\tfrac{a}{b}y+b^{-1}y^2\bigr)\,R(y)\Bigr)^{-1},$$ where $R(y)$ is the value at $y$ of the polynomial `rsEulerPoly (a / b) b⁻¹ a b 0`, i.e. of the sextic $1+C(-(Ae_1))X+C(A^2e_2+Be_1^2-2Be_2)X^2+C(-(A^3e_3)-ABe_1e_2+3ABe_3)X^3+C(A^2Be_1e_3-2B^2e_1e_3+B^2e_2^2)X^4+C(-(AB^2e_2e_3))X^5+C(B^3e_3^2)X^6$ specialised at $A=a/b$, $B=b^{-1}$, $e_1=a$, $e_2=b$, $e_3=0$, which collapses to the quartic $1-\tfrac{a^2}{b}y+\bigl(2\tfrac{a^2}{b}-2\bigr)y^2-\tfrac{a^2}{b}y^3+y^4$. Thus the reciprocal of a degree-nine product has a logarithm with non-negative Taylor coefficients subject to the stated growth bound on the disc of radius $N^{-1}$.
--
--   The displayed product is the local Euler factor, at an unramified place with $y$ the local parameter, of the degree-nine Rankin–Selberg $L$-function attached to the triple consisting of the trivial factor, a rank-two factor with trace $a$ and determinant $b$, and its contragredient; the hypotheses encode unitarity (stability of the inverse root pair under $z\mapsto\bar z^{-1}$) together with a bound on the roots in terms of $N$. The positivity and growth of the logarithmic coefficients is what feeds a Landau-type argument, and the statement is used in proving non-vanishing at $s=1$ for the twisted Euler product of an automorphic form over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 9 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) =
          ((1 - y) * (1 - a * y + b * y ^ 2) * (1 - (a / b) * y + b⁻¹ * y ^ 2) *
            (rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by sorry
