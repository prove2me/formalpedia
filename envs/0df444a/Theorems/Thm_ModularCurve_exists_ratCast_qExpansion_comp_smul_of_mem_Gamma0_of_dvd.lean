-- Prove2me | Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd
-- name    : ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c20b6972-0661-5848-b67f-fb0aa7df31df
-- title:
--   Rationality of q-expansions at the Atkin–Lehner translates
-- statement:
--   Let $M,\ell\ge 1$ and $m\ge 0$ be natural numbers and let $G\colon\mathfrak H\to\mathbb C$ be a function on the upper half-plane which is holomorphic in the sense of being `MDifferentiable` for the standard complex model with values in $\mathbb C$. Assume: (i) $G(g\tau)=G(\tau)$ for every $\tau$ and every $g$ in $\Gamma_1(M)\cap\Gamma_0(M\ell)$, the meet of the two congruence subgroups of $\mathrm{SL}_2(\mathbb Z)$; (ii) for every $\alpha\in\mathrm{SL}_2(\mathbb Z)$ the product $\bigl(\tau\mapsto G(\alpha\tau)\bigr)\cdot\Delta^{m}$, with $\Delta$ the weight $12$ discriminant form, is bounded as $\operatorname{Im}\tau\to\infty$; (iii) every coefficient of the width $1$ $q$-expansion of $G\cdot\Delta^{m}$, in the parameter $e^{2\pi i\tau}$, lies in $\mathbb Q$, i.e. for each $n$ there is $r\in\mathbb Q$ with that $n$-th coefficient equal to $r$. Let $\gamma\in\Gamma_0(M)$ have lower-right entry $\gamma_{11}$ divisible by $\ell$, and let $n$ be a natural number. Then the $n$-th coefficient of the width $\ell$ $q$-expansion, in the parameter $e^{2\pi i\tau/\ell}$, of $\bigl(\tau\mapsto G(\gamma\tau)\bigr)\cdot\Delta^{m}$ is a rational number.
--
--   This is the rationality statement for the Atkin–Lehner involution at $\ell$: the elements $\gamma\in\Gamma_0(M)$ with $\ell\mid d$ carry $\infty$ to the cusps of $\Gamma_1(M)\cap\Gamma_0(M\ell)$ above the cusp $0$ of $X_0(\ell)$, and the assertion is that rationality of the expansion of $G\cdot\Delta^m$ at $\infty$ propagates to the expansions there, in the local parameter of width $\ell$. It is used by [`ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even`](thm.html#ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even) in the analysis of integrality of $q$-expansions under Atkin–Lehner slashing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ),
      ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion ℓ
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by sorry
