-- Prove2me | Theorems.Thm_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
-- name    : MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/983e8692-411d-5262-af92-a48ccb140431
-- title:
--   Laurent coefficients of a functional equation on an annulus
-- statement:
--   Let $T$ be a measurable space with a measure $\mu$, let $d \colon T \to \mathbb{Z}$ be measurable, and let $g \colon T \to \mathbb{C}$ be a function. Let $a, b$ be reals with $0 \le a < b$, and assume that for every $Y \in \mathbb{C}$ with $a < \|Y\| < b$ the function $t \mapsto g(t)\, Y^{d(t)}$ is $\mu$-integrable (the power being the integer power of $Y$). Let $Q, P \in \mathbb{C}[X]$ and $n \in \mathbb{Z}$, and assume the functional equation
--   $$\Big(\int_T g(t)\, Y^{d(t)}\, d\mu(t)\Big)\, Q(Y) = P(Y)\, Y^{n}$$
--   for all $Y$ in the open annulus $a < \|Y\| < b$. Then for every $j \in \mathbb{Z}$,
--   $$\sum_{i \in \operatorname{supp} Q} Q_i \int_{d^{-1}(\{j - i\})} g \, d\mu = \begin{cases} P_{\,j-n} & \text{if } n \le j,\\ 0 & \text{otherwise,}\end{cases}$$
--   where the sum is over the finite support of the coefficients of $Q$, $Q_i$ denotes the coefficient of $X^{i}$ in $Q$, and on the right the coefficient of $P$ is taken in degree $(j-n)$, viewed as a natural number. That is, the functional equation holds coefficientwise for the Laurent expansion indexed by the level sets of $d$.
--
--   This is the coefficientwise (Laurent) form of a one-variable functional equation for an integral transform $Y \mapsto \int g\, Y^{d}$ on an annulus: the shells $d^{-1}(\{\ell\})$ produce the Laurent coefficients, and uniqueness of Laurent coefficients on an annulus transfers the identity $Z(Y)Q(Y) = P(Y)Y^n$ to each coefficient. It is used by [`MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq`](thm.html#MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq), and rests on the shell decomposition [`MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow`](thm.html#MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow) together with [`Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero`](thm.html#Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
    {T : Type*} [MeasurableSpace T] (μ : Measure T) (d : T → ℤ) (hd : Measurable d)
    (g : T → ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → Integrable (fun t => g t * Y ^ d t) μ)
    (Q P : Polynomial ℂ) (n : ℤ)
    (hfe : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b →
      (∫ t, g t * Y ^ d t ∂μ) * Q.eval Y = P.eval Y * Y ^ n)
    (j : ℤ) :
    ∑ i ∈ Q.support, Q.coeff i * ∫ t in d ⁻¹' {j - (i : ℤ)}, g t ∂μ =
      if n ≤ j then P.coeff (j - n).toNat else 0 := by sorry
