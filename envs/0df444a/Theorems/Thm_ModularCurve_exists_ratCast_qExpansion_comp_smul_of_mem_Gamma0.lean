-- Prove2me | Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0
-- name    : ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/cb08ea2d-4876-503d-be52-c4d57dff919d
-- title:
--   Rationality of q-expansions preserved under Γ₀(N)
-- statement:
--   Let $N\ge 1$ and $m\ge 0$ be natural numbers, let $\Delta$ be the weight-$12$ discriminant cusp form `ModularForm.discriminant`, and let $G\colon\mathfrak H\to\mathbb C$ be a function on the upper half-plane which is holomorphic (differentiable for the complex model structure on $\mathfrak H$ and on $\mathbb C$). Assume: $G(g\tau)=G(\tau)$ for every $g\in\Gamma_1(N)$ and every $\tau\in\mathfrak H$; for every $\alpha\in\mathrm{SL}_2(\mathbb Z)$ the product of $\tau\mapsto G(\alpha\tau)$ with $\Delta^m$ is bounded at $i\infty$; and every coefficient of the $q$-expansion of width $1$ (that is, in $q=e^{2\pi i\tau}$) of $G\,\Delta^m$ is the image of a rational number under $\mathbb Q\to\mathbb C$. Let $\gamma\in\Gamma_0(N)$ and let $n$ be a natural number. Then the $n$-th coefficient of the width-$1$ $q$-expansion of the product of $\tau\mapsto G(\gamma\tau)$ with $\Delta^m$ is again the image of a rational number; that is, there is $r\in\mathbb Q$ with that coefficient equal to $(r:\mathbb C)$.
--
--   This is the rationality statement underlying the arithmetic of the diamond operators: substitution by $\gamma\in\Gamma_0(N)$, which normalises $\Gamma_1(N)$, preserves the field of modular functions for $\Gamma_1(N)$ whose Fourier expansion at the cusp $\infty$ has rational coefficients. It is used by [`ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0`](thm.html#ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0), the corresponding assertion phrased with the slash action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 (N : ℕ) [NeZero N] (m : ℕ)
    (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by sorry
