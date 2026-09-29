-- Prove2me | Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- name    : ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/f4ec4dd9-d688-5788-bcb9-53d88c6aa14c
-- title:
--   Unique lifting of Γ₀(p^k) kernel polynomials along nilpotent surjections
-- statement:
--   Let $T$ and $T'$ be commutative rings (in a common universe), let $\pi : T \to T'$ be a surjective ring homomorphism whose kernel is nilpotent in the sense that $(\ker \pi)^n = 0$ for some $n$, let $W$ be a Weierstrass curve over $T$ whose discriminant $\Delta_W$ is a unit, let $p$ be a prime and $k$ a natural number, and assume the image of $p$ in $T$ is a unit. Suppose $h' \in T'[X]$ satisfies [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for the base change $W \otimes_\pi T'$ at $p, k$; that is: if $p^k = 2$, then $\deg h' \le 1$, the coefficient of $X$ in $h'$ is $1$, and $h'$ divides $\Psi_2^2$ of the base-changed curve; otherwise $\deg h' \le \varphi(p^k)/2$, the coefficient of $h'$ in degree $\varphi(p^k)/2$ is $1$, the product $h' \cdot \mathrm{pre}\Psi_{p^{k-1}}$ divides $\mathrm{pre}\Psi_{p^k}$ (with $k-1$ truncated natural subtraction), and $h'$ divides $\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h'$ for every natural $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$, all formed for $W \otimes_\pi T'$. The conclusion is that there is exactly one $h \in T[X]$ with $\pi_*(h) = h'$ which satisfies the same predicate [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $W$ at $p, k$.
--
--   This is the infinitesimal lifting property of $\Gamma_0(p^k)$-structures in the form of kernel polynomials: when $p$ and the discriminant are invertible the corresponding moduli problem is étale, so its sections lift uniquely across a surjection with nilpotent kernel. It feeds the lifting of full level-$p^k$ tuples and the comparison of the actions on level components used in the gluing of the associated moduli spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.lean

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open Polynomial

theorem ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hp : IsUnit ((p : ℕ) : T))
    (h' : Polynomial T') (hh' : ModularCurve.IsGamma0PowAt (W.map π) p k h') :
    ∃! h : Polynomial T, h.map π = h' ∧ ModularCurve.IsGamma0PowAt W p k h := by sorry
