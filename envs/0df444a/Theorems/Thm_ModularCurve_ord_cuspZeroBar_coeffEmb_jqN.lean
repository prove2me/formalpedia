-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN
-- name    : ModularCurve.ord_cuspZeroBar_coeffEmb_jqN
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/766b738d-9b69-53aa-919d-595022136220
-- title:
--   Order -1 of j(q^N) at the cusp zero
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and assume the hypothesis `IsFrickeAutFull N (frickeInvolutionFull N)`: the distinguished $\mathbb{Q}$-algebra automorphism `frickeInvolutionFull N` of the modular function field `modularFunctionFieldFull N` (the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$) carries, for every factorisation $a \cdot b = N$ with $a, b$ nonzero, the element $j(q^a)$ to $j(q^b)$, where $j(q^a)$ denotes the image of the Laurent series `jq` under the substitution $q \mapsto q^a$ given by `qExpand ℚ a`. Consider the place `cuspZeroBar N` of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$, namely the translate of the cusp at infinity `cuspInftyBar N` by `frickeInvolutionBar N`, the automorphism of the base-changed field induced by `frickeInvolutionFull N`. The assertion is that the order function of this place, $f \mapsto -\log$ of its adic valuation at $f$, takes the value $-1$ on the element of `modularFunctionFieldBar N` obtained by applying the coefficient embedding $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$ to $j(q^N)$.
--
--   Classically this records that the function $j(q^N)$, which is a uniformiser-like parameter at the cusp $\infty$ of $X_0(N)$, has a simple pole at the cusp $0$; it is the case $(a,b) = (1,N)$ of the general formula for orders of the functions $j(q^b)$ at the cusp $0$. It is used in the computation of orders of modular units and in the cusp rules for place specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspZeroBar_coeffEmb_jqN (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : (cuspZeroBar N).ord ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩ = -1 := by sorry
