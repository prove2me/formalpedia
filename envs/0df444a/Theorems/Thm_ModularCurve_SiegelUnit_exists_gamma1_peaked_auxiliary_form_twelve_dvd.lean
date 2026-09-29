-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd
-- name    : ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/9f9d447e-a604-5813-b718-9e1b6ad99a07
-- title:
--   Peaked auxiliary form on Γ₁(N) of weight divisible by 12
-- statement:
--   Let $N$ be a natural number with $N \ge 2$. Then there exist an integer $w$, natural numbers $m_0$ and $a$, a real number $\delta$, and a modular form $\vartheta$ of weight $w$ for the image of $\Gamma_1(N)$ in $\mathrm{GL}_2(\mathbb{R})$, such that: $w$ is divisible by $12$; $w < 12 m_0$; $\delta > 0$; for every $n$ the number $N^a$ times the $n$-th coefficient of the width-$N$ $q$-expansion of $\vartheta \mid[w] S$, where $S = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$, is integral over $\mathbb{Z}$; the $n$-th coefficient of the width-$1$ $q$-expansion of $\vartheta$ vanishes for all $n < m_0$ and is nonzero for $n = m_0$; $N^a$ times the inverse of that $m_0$-th coefficient is integral over $\mathbb{Z}$; $N^a$ times each coefficient of the width-$1$ $q$-expansion of $\vartheta$ is integral over $\mathbb{Z}$; and, finally, for every $\beta \in \mathrm{SL}_2(\mathbb{Z})$ such that neither $\beta$ nor $-\beta$ lies in $\Gamma_1(N)$ and such that for every $j \in \mathbb{Z}$ neither $\beta T^{j} S^{-1}$ nor its negative lies in $\Gamma_1(N)$ (with $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$), one has $\vartheta \mid[w] \beta = O\bigl(\exp(-2\pi(m_0+\delta)\,\mathrm{Im}\,\tau)\bigr)$ as $\mathrm{Im}\,\tau \to \infty$.
--
--   This produces the auxiliary modular form on $\Gamma_1(N)$ used in the trace/peak argument: its width-$1$ expansion at $\infty$ begins exactly in degree $m_0$ with a coefficient whose inverse is integral after clearing powers of $N$, while at every cusp other than the classes of $\infty$ and $0$ (the two excluded families of matrices $\beta$) the slashed form decays faster than $q^{m_0}$. The form is assembled from Siegel units and a power of the discriminant $\Delta$, and the statement is used by [`ModularCurve.exists_gamma1_peaked_auxiliary_form`](thm.html#ModularCurve.exists_gamma1_peaked_auxiliary_form).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd (N : ℕ) (hN : 2 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      12 ∣ w ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
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
