-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
-- name    : LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/a446eab9-f3d2-51c8-9ab3-a00612e179aa
-- title:
--   Logarithm of a unitary self-dual Rankin–Selberg local factor
-- statement:
--   Let $a,b\in\mathbb{C}$ and let $N$ be a real number with $N>1$. Assume $\lVert b\rVert=1$, that $a^{2}=tb$ for some real $t\ge 0$, and that $\lVert a\rVert^{2}<N+2+N^{-1}$. Then there exists a sequence $c:\mathbb{N}\to\mathbb{R}$ with $c_{0}=0$, $c_{1}=\lVert a\rVert^{2}$, $c_{m}\ge 0$ for all $m$, and $c_{m}\le 4N^{m}$ for all $m$, such that for every $y\in\mathbb{C}$ with $\lVert y\rVert<N^{-1}$ the family $m\mapsto c_{m}y^{m}$ is summable in $\mathbb{C}$ and $$\exp\Bigl(\sum_{m}c_{m}y^{m}\Bigr)=\bigl(P(y)\bigr)^{-1},$$ where $P$ is the polynomial `rsEulerPoly (a / b) b⁻¹ a b 0`, i.e. the specialisation of the six-degree Rankin–Selberg Euler polynomial $\mathrm{rsEulerPoly}(A,B,e_1,e_2,e_3)$ at $A=a/b$, $B=b^{-1}$, $e_1=a$, $e_2=b$, $e_3=0$; since $e_3=0$ the coefficients of $X^{5}$ and $X^{6}$ vanish and $$P(X)=1-\tfrac{a^{2}}{b}X+\Bigl(2\tfrac{a^{2}}{b}-2\Bigr)X^{2}-\tfrac{a^{2}}{b}X^{3}+X^{4}.$$ In particular $P(y)\neq 0$ on the disc $\lVert y\rVert<N^{-1}$, as the left-hand side is a value of $\exp$.
--
--   This is the local input to the Rankin–Selberg positivity argument: at a place where the local Hecke data $(a,b)$ is unitary ($\lVert b\rVert=1$) and self-dual ($a^{2}/b$ real and non-negative), the inverse local factor of the convolution of the local component with its conjugate is the exponential of a power series with non-negative coefficients whose linear coefficient is $\lVert a\rVert^{2}$, with the stated growth bound on the disc of radius $N^{-1}$. It is used by [`AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.exists_tsum_norm_a_sq_mul_rpow_absNorm_le_log_of_isArithGenuineCuspRealizable) to convert the analytic behaviour of a Rankin–Selberg $L$-function into a bound on sums of $\lVert a_{\mathfrak p}\rVert^{2}$ weighted by powers of the absolute norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_eval_rsEulerPoly_self_of_norm_eq_one
    (a b : ℂ) (N : ℝ) (hN : 1 < N) (hb : ‖b‖ = 1) (hab : ∃ t : ℝ, 0 ≤ t ∧ a ^ 2 = (t : ℂ) * b)
    (ha : ‖a‖ ^ 2 < N + 2 + N⁻¹) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧ c 1 = ‖a‖ ^ 2 ∧ (∀ m : ℕ, 0 ≤ c m) ∧ (∀ m : ℕ, c m ≤ 4 * N ^ m) ∧
      ∀ y : ℂ, ‖y‖ < N⁻¹ →
        Summable (fun m : ℕ => (c m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (c m : ℂ) * y ^ m) = ((rsEulerPoly (a / b) b⁻¹ a b 0).eval y)⁻¹ := by sorry
