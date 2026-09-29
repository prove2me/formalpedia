-- Prove2me | Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
-- name    : ModularCurve.cuspZeroBar_ne_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/d2518335-7eea-5c45-a9c2-b57c920ec522
-- title:
--   The cusps ̄ 0 and ∞̄ are distinct for N>1
-- statement:
--   Let $N$ be a nonzero natural number. Assume first that the distinguished automorphism `frickeInvolutionFull N` of the modular function field $F_N^{\mathrm{full}} =$ `modularFunctionFieldFull N` — the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions attached to $N$ — satisfies the predicate `IsFrickeAutFull N`, that is: for every factorisation $ab = N$ into nonzero natural numbers it carries the element of $F_N^{\mathrm{full}}$ given by the $q$-series $\mathrm{qExpand}\,a$ applied to the $q$-expansion of $j$ (substituting $q \mapsto q^a$) to the element given by $\mathrm{qExpand}\,b$ applied to that same expansion. Assume further that $1 < N$. The conclusion is that the two places `cuspZeroBar N` and `cuspInftyBar N` of the base-changed field `modularFunctionFieldBar N` $= \bar{\mathbb{Q}}\cdot F_N^{\mathrm{full}} \subseteq \bar{\mathbb{Q}}((q))$ over $\bar{\mathbb{Q}}$ are distinct. Here `cuspInftyBar N` is the $q$-adic place at $q = 0$, given by the valuation subring of elements of nonnegative order, witnessed by the coefficient-extended $q$-expansion of $j$ (of order $-1$); and `cuspZeroBar N` is its translate under the Galois-type action of `frickeInvolutionBar N`, the $\bar{\mathbb{Q}}$-automorphism of `modularFunctionFieldBar N` induced by `frickeInvolutionFull N`.
--
--   This is the statement that, on the modular curve attached to $F_N^{\mathrm{full}}$ with $N > 1$, the cusp $0$ (the Fricke translate of $\infty$) is not the cusp $\infty$; it is what gives the cuspidal divisor $(\bar 0) - (\bar\infty)$ content. It is used by the results on the cuspidal divisor class, among them the nonvanishing of that class and the bound on its order, and by the classification of the places lying over the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.cuspZeroBar_ne_cuspInftyBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) (hN : 1 < N) : cuspZeroBar N ≠ cuspInftyBar N := by sorry
