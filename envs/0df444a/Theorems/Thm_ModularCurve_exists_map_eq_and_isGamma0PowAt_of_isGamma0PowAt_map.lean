-- Prove2me | Theorems.Thm_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
-- name    : ModularCurve.exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a2ed3124-6d7d-5d90-9fe7-54123499453f
-- title:
--   Descent of a Γ₀(p^k) kernel polynomial to an integrally closed domain
-- statement:
--   Let $R_0$ be an integrally closed domain with fraction field $K$ (both in the same universe), let $W_0$ be a Weierstrass curve over $R_0$, let $p,k$ be natural numbers such that the image of $p$ in $R_0$ is a unit, and let $h' \in K[X]$. Assume that $h'$ satisfies [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for the base change $W_0 \otimes_{R_0} K$ and the pair $(p,k)$: that is, if $p^k = 2$ then $\deg h' \le 1$, the coefficient of $X$ in $h'$ is $1$, and $h'$ divides $\Psi_2^2$ of the base-changed curve; while if $p^k \ne 2$ then $\deg h' \le \varphi(p^k)/2$, the coefficient of $X^{\varphi(p^k)/2}$ in $h'$ is $1$, the product $h' \cdot \mathrm{pre}\Psi_{p^{k-1}}$ divides $\mathrm{pre}\Psi_{p^k}$, and $h'$ divides $\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h'$ for every integer $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$, all for the curve over $K$. The conclusion is that there exists $h_0 \in R_0[X]$ whose image under $R_0[X] \to K[X]$ is $h'$ and which satisfies [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $W_0$, $p$ and $k$, i.e. the same list of degree, coefficient, divisibility and scalar-stability conditions over $R_0$.
--
--   This is a descent statement of Gauss-lemma type: a $\Gamma_0(p^k)$ kernel datum on the generic fibre of an integral Weierstrass model is already defined over the base, provided $p$ is invertible there. It is used through its tuple version [`ModularCurve.exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map`](thm.html#ModularCurve.exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map) in the construction of integral models of the relevant moduli data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem ModularCurve.exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (p k : ℕ) (hp : IsUnit ((p : ℕ) : R₀))
    (h' : Polynomial K) (hh' : ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) p k h') :
    ∃ h₀ : Polynomial R₀, h₀.map (algebraMap R₀ K) = h' ∧ ModularCurve.IsGamma0PowAt W₀ p k h₀ := by sorry
