-- Prove2me | Theorems.Thm_Helfgott_regularized_primitive_strip_band_multiplicity_numerical_bound
-- name    : Helfgott.regularized_primitive_strip_band_multiplicity_numerical_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T22:18:23.797059+00:00
-- url     : https://prove2.me/theorems/d63a3ac7-d084-4dc7-b387-584aa07ca650
-- title:
--   Numerical unit-band zero multiplicity bound for primitive Dirichlet L-functions
-- statement:
--   Let $\chi$ be a primitive Dirichlet character of conductor $1\le q\le300000$. Set $H=L(s,\chi)$ for a nonprincipal character, and $H=(s-1)\zeta(s)$ with its removable value at $s=1$ for the primitive principal character. For every $T\ge8$ and every finite set $Z$ lying in $-1/2\le\Re\rho\le2$ and $T\le|\Im\rho|\le T+1$, the sum of the exact analytic multiplicities of $H$ at those points is at most $8000(1+T)$. Nonzero points have multiplicity zero. The estimate is unconditional, uniform in the conductor, and covers both signs of the imaginary part. It provides an explicit numerical count for the high-zero tail in the Goldbach major-arc certificate.
-- source:
--   Goldbach major-arc zero-tail setup: https://arxiv.org/html/1312.7748v2. Mathlib contributors: Dirichlet analytic continuation and functional equation, Mellin transforms, Gamma convexity and reflection, Jensen formula and analytic orders. Complete original numerical Abel-remainder and strip-growth bounds. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.Order
open Complex Set
open scoped Classical

namespace Helfgott

theorem regularized_primitive_strip_band_multiplicity_numerical_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive)
    (hq : q≤300000) (T : ℝ) (hT : 8≤T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z,-(1/2 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 2 ∧ T ≤ |ρ.im| ∧ |ρ.im| ≤ T+1) :
    let H : ℂ → ℂ := if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction
    (∑ ρ ∈ Z,(analyticOrderNatAt H ρ : ℝ))≤8000*(1+T) := by sorry

end Helfgott
