-- Prove2me | Theorems.Thm_ModularCurve_separable_cosetTwoVarPoly
-- name    : ModularCurve.separable_cosetTwoVarPoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/f5a745d3-07cf-5129-8a5a-38f2d5047d74
-- title:
--   Separability of the coset polynomial for a simple-pole series
-- statement:
--   Let $K$ be a field, let $N$ be a natural number with $N \neq 0$, let $\zeta \in K^{\times}$ be a primitive $N$-th root of unity, and let $J$ be a Laurent series over $K$ whose coefficient in degree $-1$ is non-zero and whose coefficients in all degrees $m < -1$ vanish (so $J$ has a pole of exact order one with non-zero residue). The assertion is that the polynomial [`ModularCurve.cosetTwoVarPoly ζ N J`](def/ModularCurve_PrimCosetReps.html#L44) over the field of Laurent series $K((t))$ is separable, i.e. coprime to its derivative. By definition this polynomial is the product, over the triples $t = (a,b,d)$ of natural numbers lying in [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8) — those $(a,b,d)$ with $a, b, d \le N$, $a d = N$, $b < d$ and $\gcd(a,\gcd(b,d)) = 1$ — of the monic linear factors $X - C(\mathrm{cosetConj}\,\zeta\,J\,t)$, where the coefficient $\mathrm{cosetConj}\,\zeta\,J\,(a,b,d)$ is $0$ when $a = 0$ and otherwise the series $\mathrm{cosetSubst}\,\zeta\,a\,b\,J$, namely $J$ twisted by $\zeta^{ab}$ and then expanded in $t^{a^{2}}$, i.e. $J(\zeta^{ab}t^{a^{2}})$. Equivalently, the conclusion says that these $\#\,$`primCosetReps N` Laurent series are pairwise distinct.
--
--   This is the Laurent-series, arbitrary-characteristic form of the classical statement that the conjugates $j((a\tau+b)/d)$ of the modular function $j$ attached to the primitive coset representatives of level $N$ are pairwise distinct, so that the modular polynomial of level $N$ has no repeated roots; primitivity of $\zeta$ is the only input about the characteristic. It is used in the identification of the level-$N$ modular polynomial with this coset product and in the separability of its reduction over a rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_separable_cosetTwoVarPoly.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.separable_cosetTwoVarPoly (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0) :
    (ModularCurve.cosetTwoVarPoly ζ N J).Separable := by sorry
