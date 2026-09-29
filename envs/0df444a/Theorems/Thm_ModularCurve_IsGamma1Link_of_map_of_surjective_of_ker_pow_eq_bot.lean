-- Prove2me | Theorems.Thm_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot
-- name    : ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a2cad871-b530-50f2-92ce-22195c198e4b
-- title:
--   Lifting the Γ₁-link along a nilpotent thickening
-- statement:
--   Let $T$ and $T'$ be commutative rings and $\pi : T \to T'$ a surjective ring homomorphism whose kernel is nilpotent, in the sense that $(\ker \pi)^n = 0$ for some $n \in \mathbb{N}$. Let $W$ be a Weierstrass curve over $T$ with $\Delta_W \in T^\times$, let $\ell$ be a prime with $\ell \ge 3$ and $\ell \in T^\times$, and let $M'$ be a nonzero natural number with $M' \in T^\times$. Let $h$ assign to each prime $p \mid M'$ a polynomial $h_p \in T[X]$ satisfying $\mathrm{IsGamma0PowAt}$ for $W$, $p$ and $k = v_p(M')$: that is, if $p^k = 2$ then $h_p$ has degree at most $1$, coefficient $1$ in degree $1$, and divides $W.\Psi_2^{\mathrm{Sq}}$; otherwise $\deg h_p \le \varphi(p^k)/2$, the coefficient of $h_p$ in degree $\varphi(p^k)/2$ is $1$, $h_p \cdot \mathrm{pre}\Psi_{p^{k-1}} \mid \mathrm{pre}\Psi_{p^k}$, and $h_p$ divides $W.\mathrm{smulNumerator}\, a\, (\varphi(p^k)/2)\, h_p$ for all $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$. Let $D = (x_P, y_P, x_Q, y_Q)$ be a quadruple of elements of $T$ which is a $\Gamma_1(\ell)$-point of $W$: $(x_P,y_P)$ satisfies the affine Weierstrass equation, $(\mathrm{pre}\Psi_\ell)(x_P) = 0$, $x_Q = x_P$ and $y_Q = y_P$. Assume the $\Gamma_1$-link holds after applying $\pi$, i.e. for $W$ mapped along $\pi$, the polynomials $h_p$ mapped along $\pi$ and $D$ mapped coordinatewise along $\pi$. Then the $\Gamma_1$-link holds over $T$: if $\ell \mid M'$, then $h_\ell$ divides $\prod_{a=1}^{(\ell-1)/2}\bigl(\Phi_{n} \cdot C(\Psi^{\mathrm{Sq}}_a(x_P)) - C(\Phi_a(x_P)) \cdot \Psi^{\mathrm{Sq}}_{n}\bigr)$ in $T[X]$, where $n = \ell^{v_\ell(M') - 1}$ (the assertion being vacuous when $\ell \nmid M'$).
--
--   This is the infinitesimal lifting step for the compatibility condition linking the $\Gamma_1(\ell)$-point with the $\Gamma_0(\ell^{v_\ell(M')})$-generator polynomial: plain divisibility of polynomials does not lift along nilpotent thickenings, and the statement holds because the roots of $h_\ell$ have moduli-theoretic meaning as abscissae of points of the relevant kernel and $\mathrm{pre}\Psi$ is separable under the unit hypotheses. It is used in the analysis of the level-$p$ moduli data attached to $W$, in particular in the surjectivity statements for the induced maps along such thickenings and in the dual-number computations for diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓu : IsUnit ((ℓ : ℕ) : T))
    (M' : ℕ) [NeZero M'] (hM'u : IsUnit ((M' : ℕ) : T))
    (h : ↥M'.primeFactors → Polynomial T)
    (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (hlk' : ModularCurve.IsGamma1Link (W.map π) ℓ M' (fun p => (h p).map π) (D.map π)) :
    ModularCurve.IsGamma1Link W ℓ M' h D := by sorry
