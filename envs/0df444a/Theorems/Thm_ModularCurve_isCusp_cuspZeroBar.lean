-- Prove2me | Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
-- name    : ModularCurve.isCusp_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/14c85480-1094-50db-b52c-f16742b635c1
-- title:
--   The cusp ̄ 0 is a pole of j
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $h$ be the hypothesis that the distinguished automorphism `frickeInvolutionFull N` of the field $F_N$ = `modularFunctionFieldFull N` (the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions N`) satisfies `IsFrickeAutFull N`, i.e. for every factorisation $N = ab$ into nonzero natural numbers it carries the element $\mathrm{qExpand}\,a\,(jq)$, the series obtained from $jq = q^{-1}\cdot jNumQ$ by $q \mapsto q^a$, to $\mathrm{qExpand}\,b\,(jq)$. Work in $\bar F_N$ = `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_N$ under the coefficientwise map `coeffEmb`. The assertion is that the element of $\bar F_N$ given by `coeffEmb` applied to $jq$ (its membership being furnished by the base-change membership lemma) is a cusp for the place `cuspZeroBar N`, that is, for the translate of the $q$-adic place at infinity `cuspInftyBar N` by the geometric extension `frickeInvolutionBar N` of `frickeInvolutionFull N`; here `IsCusp j v` means precisely that $j$ does not lie in the valuation subring underlying the place $v$.
--
--   This records that $j$ has a pole at the cusp $\bar 0$ of the modular curve attached to level $N$, the Fricke-transform of the cusp $\bar\infty$; it is the basic qualitative input on the behaviour of $j$ at $0$. It is used throughout the subsequent analysis of places of the modular function field, in particular in the specialisation and prolongation arguments for places over level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCusp_cuspZeroBar.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspZeroBar (N : ℕ) [NeZero N] (h : IsFrickeAutFull N (frickeInvolutionFull N)) : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspZeroBar N) := by sorry
