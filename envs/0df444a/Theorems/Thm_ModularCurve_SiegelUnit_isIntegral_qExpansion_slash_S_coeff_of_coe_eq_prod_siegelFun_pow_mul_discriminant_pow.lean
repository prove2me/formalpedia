-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- name    : ModularCurve.SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/43997538-b15b-59d5-b1c7-5d3768e49410
-- title:
--   Integrality up to a power of N of the cusp-0 expansion
-- statement:
--   Fix $N\ge 1$, a function $m\colon \mathbb{Z}/N\times\mathbb{Z}/N\to\mathbb{N}$ and $t\in\mathbb{N}$, and let $\vartheta$ be a modular form of weight $12t$ for the congruence subgroup $\Gamma_1(N)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Assume that for every $\tau$ in the upper half-plane
--   $$\vartheta(\tau)=\Bigl(\prod_{r\in\mathbb{Z}/N}\prod_{s\in\mathbb{Z}/N} g_{r,s}(\tau)^{12Nm(r,s)}\Bigr)\cdot\Delta(\tau)^{t},$$
--   where $\Delta$ is Mathlib's discriminant form `ModularForm.discriminant` and $g_{r,s}=$ [`ModularCurve.siegelFun`](def/ModularCurve_SiegelFunction.html#L10) evaluated at the least non-negative integer lifts $r.\mathrm{val}$, $s.\mathrm{val}$, that is, with $q=e^{2\pi i z}$ and $w=e^{2\pi i(rz+s)/N}$,
--   $$g_{r,s}(z)=-e^{\pi i s(r-N)/N^{2}}\,e^{\pi i((r/N)^{2}-r/N+1/6)z}\,(1-w)\prod_{n\ge 0}\bigl(1-q^{\,n+1}w\bigr)\bigl(1-q^{\,n+1}w^{-1}\bigr).$$
--   The conclusion is the existence of an exponent $a\in\mathbb{N}$ such that for every $n\in\mathbb{N}$ the complex number $N^{a}$ times the $n$-th coefficient of the width-$N$ $q$-expansion `UpperHalfPlane.qExpansion` of the weight-$12t$ slash of the underlying function of $\vartheta$ by the image in $\mathrm{GL}_2(\mathbb{R})$ of $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\in\mathrm{SL}_2(\mathbb{Z})$ is integral over $\mathbb{Z}$.
--
--   The statement expresses the algebraic integrality, after clearing a single power of $N$, of the Fourier coefficients in $q_N=e^{2\pi i\tau/N}$ of a Siegel-unit times $\Delta^{t}$ at the cusp $0$ of $\Gamma_1(N)$, the expansion being taken with width $N$ since $S T^{N} S^{-1}$ lies in $\Gamma_1(N)$. It is used in the construction of an auxiliary form on $\Gamma_1(N)$ with prescribed behaviour at the cusps, via [`ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`](thm.html#ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by sorry
