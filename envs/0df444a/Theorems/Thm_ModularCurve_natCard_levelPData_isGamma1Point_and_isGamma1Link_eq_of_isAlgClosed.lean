-- Prove2me | Theorems.Thm_ModularCurve_natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
-- name    : ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/669b1fbd-7b29-5277-9a2e-e38faefd989b
-- title:
--   Exactly ℓ-1 Γ₁(ℓ)-points linked to a Γ₀(M')-tuple
-- statement:
--   Let $\Omega$ be an algebraically closed field of characteristic zero, $\ell$ a prime with $\ell \ge 3$, and $M'$ a nonzero natural number divisible by $\ell$. Let $W_0$ be a Weierstrass curve over $\Omega$ whose discriminant $\Delta$ is a unit, and let $h$ assign to each prime factor $p$ of $M'$ a polynomial $h_p \in \Omega[X]$ satisfying [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $W_0$, $p$ and $k_p = \operatorname{ord}_p(M')$: that is, if $p^{k_p} = 2$ then $\deg h_p \le 1$, the coefficient of $X$ in $h_p$ is $1$ and $h_p \mid \Psi_2^{\mathrm{Sq}}$; otherwise $\deg h_p \le \varphi(p^{k_p})/2$, the coefficient of $h_p$ in degree $\varphi(p^{k_p})/2$ is $1$, $h_p \cdot \mathrm{pre}\Psi_{p^{k_p-1}} \mid \mathrm{pre}\Psi_{p^{k_p}}$, and $h_p \mid \mathrm{smulNumerator}\,a\,(\varphi(p^{k_p})/2)\,h_p$ for every $a$ with $2 \le a \le (p^{k_p}-1)/2$ and $p \nmid a$. The conclusion is that the number of quadruples $D = (x_P, y_P, x_Q, y_Q)$ of elements of $\Omega$ (a [`ModularCurve.LevelPData`](def/ModularCurve_KatzLevelP.html#L43)) such that, first, $(x_P, y_P)$ satisfies the affine Weierstrass equation of $W_0$, $(\mathrm{pre}\Psi_\ell)(x_P) = 0$, $x_Q = x_P$ and $y_Q = y_P$, and, second, $h_\ell$ divides $\mathrm{inLineMulPoly}(W_0, \ell, \ell^{k_\ell - 1}, x_P) = \prod_{a=1}^{(\ell-1)/2}\bigl(\Phi_n \cdot (\Psi_a^{\mathrm{Sq}})(x_P) - \Phi_a(x_P)\cdot \Psi_n^{\mathrm{Sq}}\bigr)$ with $n = \ell^{k_\ell-1}$, is exactly $\ell - 1$.
--
--   This is the counting step behind the $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell)$ level structure in Weierstrass coordinates: over an algebraically closed field, a fixed $\Gamma_0(M')$-tuple of generator-kernel polynomials admits precisely $\ell - 1$ compatible $\Gamma_1(\ell)$-points, namely the generators of the $\ell$-torsion of the cyclic subgroup cut out by $h_\ell$. It feeds the enumeration of $H_1$-level structures in [`ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed`](thm.html#ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (M' : ℕ) [NeZero M'] (hℓM' : ℓ ∣ M')
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ)
    (h : ↥M'.primeFactors → Polynomial Ω)
    (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) (h p)) :
    Nat.card {D : ModularCurve.LevelPData Ω //
        ModularCurve.IsGamma1Point W₀ ℓ D ∧ ModularCurve.IsGamma1Link W₀ ℓ M' h D} = ℓ - 1 := by sorry
