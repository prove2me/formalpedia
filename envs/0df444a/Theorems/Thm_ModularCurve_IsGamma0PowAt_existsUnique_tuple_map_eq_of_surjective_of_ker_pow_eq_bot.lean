-- Prove2me | Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
-- name    : ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/ef96b614-064a-58b6-910b-ff101008d5e1
-- title:
--   Unique lifting of Γ₀(M') kernel tuples along nilpotent thickenings
-- statement:
--   Let $\pi : T \to T'$ be a surjective homomorphism of commutative rings (in a fixed universe) whose kernel is nilpotent as an ideal, in the sense that $(\ker \pi)^n = \bot$ for some $n \in \mathbb{N}$; let $W$ be a Weierstrass curve over $T$ whose discriminant $W.\Delta$ is a unit, and let $M'$ be a natural number whose image in $T$ is a unit. Suppose given, for each prime $p$ in the set of prime factors of $M'$, a polynomial $hh'\,p \in T'[X]$ satisfying [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for the base-changed curve $W.\mathrm{map}\,\pi$ at $p$ and the exponent $k_p = \mathrm{ord}_p(M')$: that is, if $p^{k_p} = 2$ then $hh'\,p$ has degree at most $1$, coefficient $1$ in degree $1$, and divides $\Psi_2^2$ of $W.\mathrm{map}\,\pi$; otherwise $hh'\,p$ has degree at most $\varphi(p^{k_p})/2$ with leading coefficient $1$ in that degree, $hh'\,p \cdot \mathrm{pre}\Psi(p^{k_p-1})$ divides $\mathrm{pre}\Psi(p^{k_p})$, and $hh'\,p$ divides $\mathrm{smulNumerator}\,a\,(\varphi(p^{k_p})/2)\,(hh'\,p)$ for every $a$ with $2 \le a \le (p^{k_p}-1)/2$ and $p \nmid a$. Then there is a unique family $hh$ assigning to each prime factor $p$ of $M'$ a polynomial $hh\,p \in T[X]$ such that $p \mapsto (hh\,p).\mathrm{map}\,\pi$ equals $hh'$ as a function and each $hh\,p$ satisfies the same [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) condition for $W$ at $p$ and $\mathrm{ord}_p(M')$.
--
--   This is the infinitesimal (étale) lifting property of $\Gamma_0(M')$-level structures in the prime-power-tuple presentation: a level structure of level invertible on the base lifts uniquely along a nilpotent thickening. It is the input used by the $M'$-general versions of the surjectivity, tangent-space and deformation statements for the full-level moduli constructions, in place of a single call to the lifting lemma for one prime power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (M' : ℕ) (hM' : IsUnit ((M' : ℕ) : T))
    (hh' : ↥M'.primeFactors → T'[X])
    (H' : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt (W.map π) (p : ℕ) (M'.factorization (p : ℕ)) (hh' p)) :
    ∃! hh : ↥M'.primeFactors → T[X],
      (fun p => (hh p).map π) = hh' ∧
      ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (hh p) := by sorry
