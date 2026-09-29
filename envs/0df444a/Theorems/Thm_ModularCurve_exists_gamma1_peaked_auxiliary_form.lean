-- Prove2me | Theorems.Thm_ModularCurve_exists_gamma1_peaked_auxiliary_form
-- name    : ModularCurve.exists_gamma1_peaked_auxiliary_form
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/56fc1717-06cf-5e07-a521-263467019dbf
-- title:
--   Existence of a peaked auxiliary form on Γ₁(N)
-- statement:
--   Let $N$ be a natural number with $N \ge 2$ and let $k$ be an integer, subject to the hypothesis that $N \ge 3$ whenever $k$ is odd. Then there exist an integer $w$, natural numbers $m_0$ and $a$, a real number $\delta$, and a modular form $\vartheta$ of weight $w$ for the subgroup $\Gamma_1(N)$ of $\mathrm{GL}_2(\mathbb{R})$, such that: $k + w$ is even; $w < 12 m_0$; $\delta > 0$; for every $n$, $N^a$ times the $n$-th coefficient of the Fourier expansion of period $N$ of the weight-$w$ slash $\vartheta \mid_w S$, with $S \in \mathrm{SL}_2(\mathbb{Z})$ the standard order-four element, is integral over $\mathbb{Z}$; the Fourier expansion of $\vartheta$ of period $1$ has vanishing $n$-th coefficient for all $n < m_0$ and nonzero $m_0$-th coefficient; $N^a$ times the inverse of that $m_0$-th coefficient is integral over $\mathbb{Z}$, and so is $N^a$ times every coefficient of that expansion; and finally, for every $\beta \in \mathrm{SL}_2(\mathbb{Z})$ with $\beta \notin \Gamma_1(N)$ and $-\beta \notin \Gamma_1(N)$, and with $\pm\,\beta T^j S^{-1} \notin \Gamma_1(N)$ for every integer $j$, one has $\vartheta \mid_w \beta = O\bigl(\exp(-(2\pi(m_0+\delta))\,\mathrm{Im}\,\tau)\bigr)$ as $\mathrm{Im}\,\tau \to \infty$. The weight condition asserted is only the parity condition $k + w$ even, the form being obtained from one of weight divisible by $12$ and, in the odd case, an auxiliary weight-three form on $\Gamma_1(N)$ with the same integrality properties.
--
--   The form $\vartheta$ is the auxiliary input for the trace argument that bounds denominators of the Fourier expansion of $f \mid_k W_N$ for the Fricke involution $W_N$: it is peaked at the cusp $\infty$, has $N$-integral expansions at $\infty$ and at $0$, and decays strictly faster at all remaining cusps of $\Gamma_1(N)$. It is used by [`ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff`](thm.html#ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_gamma1_peaked_auxiliary_form (N : ℕ) (hN : 2 ≤ N) (k : ℤ)
    (hk : Odd k → 3 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      Even (k + w) ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by sorry
