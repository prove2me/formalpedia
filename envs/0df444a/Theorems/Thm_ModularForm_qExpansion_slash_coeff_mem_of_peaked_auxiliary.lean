-- Prove2me | Theorems.Thm_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary
-- name    : ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e60c40f1-c2de-5b34-a265-ff47249f6336
-- title:
--   Integrality at the cusp 0 via a peaked auxiliary form
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$, let $h>0$ be a natural number with $T^h\in\Gamma$, where $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and suppose $S T S^{-1}\in\Gamma$, where $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. Let $R$ be a subring of $\mathbb C$ and let $k,w$ be integers with $k+w$ even. Let $G$ be a modular form of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$, all of whose Fourier coefficients in the expansion of period $h$ lie in $R$, and let $\Theta$ be a modular form of weight $w$ for the same group whose period-$h$ Fourier coefficients also lie in $R$. Assume given a natural number $m_0$ with $w<12m_0$ such that the period-$1$ expansion of $\Theta\mid_w S$ has all coefficients in $R$, has vanishing coefficients in all degrees $n<m_0$, and has its degree-$m_0$ coefficient invertible in $R$ (some $v\in R$ with $v$ times that coefficient equal to $1$). Assume finally that for some $\delta>0$ and every $\beta\in\mathrm{SL}_2(\mathbb Z)$ with $\pm\beta T^j\notin\Gamma$ for all $j\in\mathbb Z$ and $\pm\beta S^{-1}\notin\Gamma$, one has $\Theta\mid_w\beta=O\big(e^{-2\pi(m_0+\delta)\,\mathrm{Im}\,\tau}\big)$ as $\mathrm{Im}\,\tau\to\infty$. Then for every natural number $n$ the $n$-th coefficient of the period-$1$ $q$-expansion of $G\mid_k S$ lies in $R$.
--
--   This is the analytic core of Serre's trace argument: under the hypothesis $STS^{-1}\in\Gamma$, which makes the cusp $0=S\infty$ of width one, a suitably peaked auxiliary form $\Theta$ propagates integrality of Fourier coefficients from the cusp $\infty$ to the cusp $0$. It is used in the construction of integral models of modular curves, namely to show that a power of the level times the $q$-expansion of a form twisted by the Fricke involution has integral coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ) (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ} (hkw : Even (k + w))
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ)).coeff n ∈ R)
    (m₀ : ℕ) (hm₀ : w < 12 * (m₀ : ℤ))
    (hΘS₀ : ∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0)
    (hΘS₁ : ∃ v ∈ R, v * (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1)
    (hΘS : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
        fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im))
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ R := by sorry
