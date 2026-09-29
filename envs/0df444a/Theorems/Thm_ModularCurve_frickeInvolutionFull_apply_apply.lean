-- Prove2me | Theorems.Thm_ModularCurve_frickeInvolutionFull_apply_apply
-- name    : ModularCurve.frickeInvolutionFull_apply_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/b05cbde7-94b7-5725-8452-df17b958c7a3
-- title:
--   The full Fricke map is an involution
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Write $F_N =$ `modularFunctionFieldFull N` for the intermediate field of the Laurent series field $\mathbb{Q}((q))$ over $\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the set `divisorExpansions N` of all elements of the form $\mathrm{qExpand}\,\mathbb{Q}\,d\,jq$ — the $q$-expansion of $j$ in the variable $q^d$ — for $d$ a nonzero divisor of $N$. Let `frickeInvolutionFull N` be the $\mathbb{Q}$-algebra automorphism of $F_N$ defined by choosing, if one exists, an automorphism $\sigma$ of $F_N$ over $\mathbb{Q}$ with the property `IsFrickeAutFull N σ`, namely that $\sigma\bigl(j(q^a)\bigr) = j(q^b)$ for every factorisation $a\,b = N$ into nonzero natural numbers, and taking the identity automorphism if no such $\sigma$ exists. The assertion is that for every $x \in F_N$ one has $\mathrm{frickeInvolutionFull}\,N\,\bigl(\mathrm{frickeInvolutionFull}\,N\,x\bigr) = x$; that is, this automorphism is its own inverse. The conclusion holds unconditionally, no hypothesis on the existence of a Fricke automorphism being required.
--
--   This records that the Fricke map $w_N$ on the function field $\mathbb{Q}(j(q^d) : d \mid N)$ attached to the modular curve $X_0(N)$ is an involution, in the form of the project's total (choice-based) definition. It is used in the treatment of the $\lambda$-line and the modular polynomial data, for instance in [`ModularCurve.exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub`](thm.html#ModularCurve.exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub) and in the computations with `LambdaModularPolynomialData`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frickeInvolutionFull_apply_apply.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve IntermediateField

theorem ModularCurve.frickeInvolutionFull_apply_apply (N : ℕ) [NeZero N] (x : modularFunctionFieldFull N) : frickeInvolutionFull N (frickeInvolutionFull N x) = x := by sorry
