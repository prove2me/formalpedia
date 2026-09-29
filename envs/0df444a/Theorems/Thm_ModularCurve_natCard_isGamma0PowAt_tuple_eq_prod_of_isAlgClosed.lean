-- Prove2me | Theorems.Thm_ModularCurve_natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed
-- name    : ModularCurve.natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/84a6ee4c-b55d-5726-bbdb-3eec12b35b59
-- title:
--   Counting Γ₀-power cyclic kernel tuples equals ψ(M')
-- statement:
--   Let $\Omega$ be an algebraically closed field of characteristic zero (with decidable equality), let $M'$ be a natural number with $M'\neq 0$, and let $W_0$ be a Weierstrass curve over $\Omega$ whose discriminant $\Delta$ is a unit, so that $W_0$ is elliptic. Consider the set of families $h$ indexed by the prime factors $p$ of $M'$, with $h(p)\in\Omega[X]$, such that for every such $p$ the polynomial $h(p)$ satisfies [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $W_0$ at $p$ and $k=v_p(M')$, the exponent of $p$ in the factorisation of $M'$; by definition this means: if $p^{k}=2$ then $h(p)$ has degree at most $1$, coefficient $1$ in degree $1$, and divides $W_0.\Psi_2^2$, while otherwise $h(p)$ has degree at most $\varphi(p^{k})/2$, coefficient $1$ in degree $\varphi(p^{k})/2$, the product $h(p)\cdot \mathrm{pre}\Psi_{p^{k-1}}$ divides $\mathrm{pre}\Psi_{p^{k}}$, and $h(p)$ divides $W_0.\mathrm{smulNumerator}\,a\,(\varphi(p^{k})/2)\,h(p)$ for every $a$ with $2\le a\le (p^{k}-1)/2$ and $p\nmid a$. The theorem asserts that the number of such families is $\prod_{p\mid M'} p^{\,v_p(M')-1}(p+1)$, i.e. the Dedekind $\psi$-value $\psi(M')$.
--
--   This is the count of $\Gamma_0(M')$-level structures on a fixed elliptic curve over an algebraically closed field of characteristic zero, presented in the polynomial (kernel-generator) form used throughout the project: the $\psi(M')$ cyclic subgroups of order $M'$ are encoded prime by prime by monic divisors of the division polynomials. It feeds the comparison of full-level and $\Gamma_0$-power rigid data and the counting of points of the relevant modular curves over a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.natCard_isGamma0PowAt_tuple_eq_prod_of_isAlgClosed
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]
    (M' : ℕ) [NeZero M'] (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) :
    Nat.card {h : ↥M'.primeFactors → Polynomial Ω //
        ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) (h p)} =
      ∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1) := by sorry
