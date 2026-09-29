-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- name    : ModularCurve.SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e63d339e-506d-5735-8806-e14b013d1ad4
-- title:
--   Exact q-order and integrality of a Siegel-unit form
-- statement:
--   Let $N$ be a non-zero natural number, let $m:\mathbb{Z}/N\mathbb{Z}\times\mathbb{Z}/N\mathbb{Z}\to\mathbb{N}$ satisfy $m(0,0)=0$, and let $t$ be a natural number. Let $\vartheta$ be a modular form of weight $12t$ for the congruence subgroup $\Gamma_1(N)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and assume that for every $\tau$ in the upper half-plane $$\vartheta(\tau)=\Bigl(\prod_{r}\prod_{s} \mathrm{siegelFun}\,N\,\tilde r\,\tilde s\,(\tau)^{12Nm(r,s)}\Bigr)\cdot\Delta(\tau)^{t},$$ the products running over $r,s\in\mathbb{Z}/N\mathbb{Z}$ with $\tilde r,\tilde s\in\{0,\dots,N-1\}$ the least non-negative representatives, $\Delta$ Mathlib's `ModularForm.discriminant`, and, writing $q=e^{2\pi i z}$ and $w=e^{2\pi i(rz+s)/N}$, $$\mathrm{siegelFun}\,N\,r\,s\,(z)=-e^{\pi i s(r-N)/N^{2}}\,e^{\pi i((r/N)^{2}-r/N+1/6)z}\,(1-w)\prod_{n\ge 0}\bigl(1-q^{n+1}w\bigr)\bigl(1-q^{n+1}w^{-1}\bigr).$$ Let $m_0$ be a natural number with $N\,m_0=\sum_{r}\sum_{s}m(r,s)\bigl(6\tilde r^{2}-6N\tilde r+N^{2}\bigr)+Nt$ as an identity of integers. Then there exists $a\in\mathbb{N}$ such that the width-one $q$-expansion of $\vartheta$ has $n$-th coefficient zero for all $n<m_0$, has non-zero $m_0$-th coefficient $c$, and such that $N^{a}c^{-1}$ is integral over $\mathbb{Z}$ and $N^{a}$ times each coefficient of the expansion is integral over $\mathbb{Z}$.
--
--   The form $\vartheta$ is a product of $12N$-th powers of Siegel functions times a power of the discriminant, i.e. a modular unit in the sense of Kubert–Lang multiplied by $\Delta^{t}$; the statement pins down its exact order of vanishing at the cusp $\infty$ in terms of the second Bernoulli values $6\tilde r^{2}-6N\tilde r+N^{2}=6N^{2}B_2(\tilde r/N)$ and gives uniform $N$-power integrality of its Fourier coefficients and of the inverse of the leading one. It is used in the construction of an auxiliary form on $\Gamma_1(N)$ peaked at a prescribed cusp, via [`ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`](thm.html#ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t)
    (m₀ : ℕ)
    (hm₀ : (N : ℤ) * m₀ =
      (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2
          - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ a : ℕ,
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n) := by sorry
