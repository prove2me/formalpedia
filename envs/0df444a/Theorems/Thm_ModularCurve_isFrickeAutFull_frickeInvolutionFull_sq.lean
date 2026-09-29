-- Prove2me | Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq
-- name    : ModularCurve.isFrickeAutFull_frickeInvolutionFull_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/95ed4588-80c8-5588-a768-e4a4b4a9e9f2
-- title:
--   `frickeInvolutionFull` is a Fricke automorphism at level p²
-- statement:
--   Let $p$ be a prime. Work inside the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$, and let $E_N \subseteq \mathbb{Q}((q))$ denote `modularFunctionFieldFull N`, the intermediate field obtained by adjoining to $\mathbb{Q}$ the family of series `divisorExpansions N`. For a nonzero natural $a$, `qExpand ℚ a` is the ring endomorphism of Laurent series that multiplies all exponents by $a$, so that `qExpand ℚ a jq` is the series $j(q^a)$ obtained from the $q$-expansion `jq` of the $j$-invariant; whenever $a$ divides $N$ this series lies in $E_N$, by `jqd_mem_full`. The predicate `IsFrickeAutFull N σ`, for a $\mathbb{Q}$-algebra automorphism $\sigma$ of $E_N$, asserts that for every pair of naturals $a,b$ with $a\,b = N$ and $a,b$ nonzero, $\sigma$ carries the element $j(q^a)$ of $E_N$ to the element $j(q^b)$. The automorphism `frickeInvolutionFull N` is defined by a guarded choice: it is some automorphism satisfying `IsFrickeAutFull N` if one exists, and the identity otherwise. The theorem states that at level $N = p\cdot p$ the guarded choice lands in the first branch, i.e. `frickeInvolutionFull (p * p)` does satisfy `IsFrickeAutFull (p * p)`: it interchanges $j(q^a)$ and $j(q^b)$ for each of the factorisations $a\,b = p^2$.
--
--   This identifies the Fricke automorphism of the level-$p^2$ modular function field concretely by its effect on the degeneracy elements $j(q^a)$, $a \mid p^2$, and so makes the level-$p^2$ Fricke involution usable rather than a possibly trivial default value. It is the input to the level-$p^2$ Hecke and cusp computations, being cited by [`ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq`](thm.html#ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq) and by [`ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_sq.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.isFrickeAutFull_frickeInvolutionFull_sq (p : ℕ) [hp : Fact (Nat.Prime p)] : IsFrickeAutFull (p * p) (frickeInvolutionFull (p * p)) := by sorry
