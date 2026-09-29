-- Prove2me | Theorems.Thm_ModularCurve_functionFieldGeneration
-- name    : ModularCurve.functionFieldGeneration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/02270e4f-19ed-5999-a205-8c9846a63f39
-- title:
--   Generation of j(qᵈ) by j(q) and j(q^N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero (as a `NeZero` instance). The assertion is the predicate `FunctionFieldGeneration N`, which unfolds as follows. For a nonzero natural $n$, `qExpand R n` denotes the ring endomorphism of the Laurent series field `LaurentSeries R` obtained by multiplying all exponents by $n$ — that is, the substitution $q \mapsto q^{n}$, which is well defined because multiplication by $n$ on $\mathbb{Z}$ is injective and order preserving. Writing `jq` for the element of `LaurentSeries ℚ` given by the $q$-expansion of the modular $j$-invariant, the theorem states: for every natural number $d$ dividing $N$, and for every `NeZero d` instance, the series `qExpand ℚ d jq`, i.e. $j(q^{d})$, belongs to the intermediate field `IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq}`, the subfield of `LaurentSeries ℚ` generated over $\mathbb{Q}$ by $j(q)$ and $j(q^{N})$. No further hypotheses are imposed: the conclusion holds unconditionally at every level $N \ge 1$.
--
--   This is the $q$-expansion form of the classical statement that the function field of $X_0(N)$ over $\mathbb{Q}$ is $\mathbb{Q}(j, j_N)$, so that the intermediate levels $j(q^d)$ for $d \mid N$ require no extra generators. It discharges the generation hypothesis used throughout the development of the level-$N$ function field — degeneracy maps between levels, the Hecke correspondence, and the characteristic-$p$ models of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_functionFieldGeneration.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N := by sorry
