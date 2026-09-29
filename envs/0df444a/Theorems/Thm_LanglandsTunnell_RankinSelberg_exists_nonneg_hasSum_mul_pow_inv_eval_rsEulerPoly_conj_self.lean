-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
-- name    : LanglandsTunnell.RankinSelberg.exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/5dc869e1-330d-5557-92c2-bd9b96294f27
-- title:
--   Non-negative coefficients of the local Rankin–Selberg factor P(y)⁻¹
-- statement:
--   Let $a,b$ be complex numbers. Write $\bar a,\bar b$ for their complex conjugates and consider the polynomial $\mathtt{rsEulerPoly}\,\bar a\,\bar b\,a\,b\,0$, i.e. the specialisation of $\mathtt{rsEulerPoly}$ at the pair $(\bar a,\bar b)$ and the elementary data $(e_1,e_2,e_3)=(a,b,0)$, which by the defining formula is $$P(X)=1-|a|^2X+\bigl(\bar a^2b+a^2\bar b-2|b|^2\bigr)X^2-|a|^2|b|^2X^3+|b|^4X^4,$$ the degree $5$ and $6$ terms vanishing because $e_3=0$. The assertion is that there exists a sequence $e:\mathbb N\to\mathbb R$ with $e_0=1$, $e_1=\|a\|^2$, $e_n\ge 0$ for all $n$, and $e_n\le\bigl(2(\|a\|+\|b\|+1)\bigr)^{2n}$ for all $n$, such that for every $y\in\mathbb C$ with $\|y\|\,(\|a\|+\|b\|+1)^2<1$ the family $n\mapsto e_n y^n$ (the $e_n$ viewed in $\mathbb C$) is summable with sum equal to the inverse of $P(y)$, the value of the polynomial at $y$. The non-vanishing of $P(y)$ is not asserted separately: the conclusion is an equality with the inverse, taken with the convention that the inverse of $0$ is $0$.
--
--   This is the purely local statement underlying the Rankin–Selberg method for $\mathrm{GL}_2$: the Euler factor of $L(s,\pi\times\bar\pi)$ at a place, expanded as a power series, has non-negative coefficients, the coefficient in degree $1$ being $|a|^2$ for the Hecke parameter $a$ at that place. Together with the explicit geometric bound on the coefficients it feeds the summability estimate [`AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.summable_norm_a_sq_mul_rpow_absNorm_of_isArithGenuineCuspRealizable), which is the form in which the second-moment input is used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_nonneg_hasSum_mul_pow_inv_eval_rsEulerPoly_conj_self
    (a b : ℂ) :
    ∃ e : ℕ → ℝ, e 0 = 1 ∧ e 1 = ‖a‖ ^ 2 ∧ (∀ n : ℕ, 0 ≤ e n) ∧
      (∀ n : ℕ, e n ≤ (2 * (‖a‖ + ‖b‖ + 1)) ^ (2 * n)) ∧
      ∀ y : ℂ, ‖y‖ * (‖a‖ + ‖b‖ + 1) ^ 2 < 1 →
        HasSum (fun n : ℕ => (e n : ℂ) * y ^ n)
          ((rsEulerPoly ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) a b 0).eval y)⁻¹ := by sorry
