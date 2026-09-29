-- Prove2me | Theorems.Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
-- name    : ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/288a97f3-029f-5b98-b6f6-22b97bff878f
-- title:
--   Bounded denominators for Fricke functions of level N
-- statement:
--   Fix a natural number $N$, assumed non-zero. Let $L$ assign to each point $\tau$ of the upper half-plane a pair of periods, subject to the hypothesis that for every $\tau$ the first period of $L\tau$ is $\tau$ and the second is $1$, so that $L\tau$ presents the lattice $\mathbb{Z}\tau+\mathbb{Z}$. Let $W$ assign to each $v\in(\mathbb{Z}/N)^2$ a function on the upper half-plane, subject to the hypothesis that for all $v$ and $\tau$, $W_v(\tau)=(2\pi i)^{-2}\,\wp_{L\tau}\!\big((\tilde v_0\tau+\tilde v_1)/N\big)$, where $\tilde v_0,\tilde v_1$ denote the canonical representatives in $\{0,\dots,N-1\}$ of the two components of $v$ and $\wp$ is the Weierstrass function of the period pair $L\tau$. Let $\mathit{fricke}$ likewise assign functions to elements $v$, subject to the hypothesis $\mathit{fricke}_v(\tau)=-\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592\cdot W_v(\tau)$. Let $v\neq 0$. Then there exists a non-zero natural number $D$ such that for every $n\in\mathbb{N}$ the product of $D$ with the $n$-th coefficient of the $q$-expansion of period $N$ of the pointwise product $\mathit{fricke}_v\cdot\Delta$ lies in the subring of $\mathbb{C}$ generated over $\mathbb{Z}$ by $\exp(2\pi i/N)$, that is, in $\mathbb{Z}[\zeta_N]$. The single $D$ works for all $n$ simultaneously.
--
--   This is the classical integrality statement for the Fricke functions of level $N$: the Fourier expansion of $f_v\Delta$ at the cusp $\infty$, in the variable $q_N=e^{2\pi i\tau/N}$, has coefficients in $\mathbb{Q}(\zeta_N)$ with denominators bounded independently of the coefficient index. It feeds the construction of models of modular curves over cyclotomic fields, being used here by [`ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`](thm.html#ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
    (N : ℕ) [NeZero N]
    (L : UpperHalfPlane → PeriodPair)
    (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), W v τ =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ,
      (D : ℂ) * (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant)).coeff n ∈
        Algebra.adjoin ℤ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} : Set ℂ) := by sorry
