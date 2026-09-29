-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
-- name    : ModularCurve.ord_cuspZeroBar_coeffEmb_jq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9293ce98-c7e6-5850-ab88-a8ee43c01493
-- title:
--   Order of j at the cusp 0 equals -N
-- statement:
--   Let $N$ be a nonzero natural number, and assume that the chosen automorphism `frickeInvolutionFull N` of the level-$N$ modular function field `modularFunctionFieldFull N` — the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions `divisorExpansions N` — satisfies the predicate `IsFrickeAutFull N`: for all natural numbers $a,b$ nonzero with $ab=N$ it sends the Laurent series $j(q^a)$, i.e. `qExpand ℚ a jq`, to $j(q^b)$, where `jq` is $q^{-1}$ times the power series $j$-numerator over $\mathbb{Q}$. Consider the element of `modularFunctionFieldBar N`, the base change of `modularFunctionFieldFull N` to an intermediate field of $\overline{\mathbb{Q}}((q))$, obtained by applying $\mathbb{Q}\to\overline{\mathbb{Q}}$ to the coefficients of `jq`. The assertion is that its order at the place `cuspZeroBar N` equals $-N$ in $\mathbb{Z}$. Here `cuspZeroBar N` is the translate, under the geometric automorphism induced by `frickeInvolutionFull N`, of the $q$-adic place `cuspInftyBar N` of `modularFunctionFieldBar N` determined by `jq`, and the order of an element at a place is minus the logarithm of its $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This records the classical fact that the modular function $j$ has a pole of order $N$ at the cusp $0$, so that $0$ is ramified of degree $N$ over the $j$-line. It is used in the construction of functions with prescribed divisors at the cusps, in the place-specialisation and prolongation arguments and in the Riemann–Roch computations of the cuspidal class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_jq (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ = -N := by sorry
