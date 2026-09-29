-- Prove2me | Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
-- name    : ModularCurve.isCusp_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/4313767f-f0d3-562b-83e0-50a9b85632e4
-- title:
--   The place at infinity is a cusp for j
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. Consider the field $F_N$ of modular functions of level $N$ obtained by base change of coefficients: starting from `modularFunctionFieldFull N`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions `divisorExpansions N`, one forms `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of `modularFunctionFieldFull N` under the coefficientwise ring map `coeffEmb` induced by $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$. Let $j$ denote the distinguished element of `modularFunctionFieldBar N` given by the image of the $q$-expansion `jq` under `coeffEmb`, together with the membership witness coming from the fact that `jq` lies in `modularFunctionFieldFull N`. Let `cuspInftyBar N` be the place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ defined as `qInftyPlaceBar` for this field, whose valuation subring is `qIntegersBar` and whose construction is witnessed by the fact that the $q$-series order of $j$ is $-1$. The conclusion is that $j$ satisfies the project's predicate `IsCusp` at this place, that is, $j$ does not belong to the valuation subring of `cuspInftyBar N`.
--
--   This records that the place $q = 0$ of the function field of the modular curve of level $N$ over $\overline{\mathbb{Q}}$ is a pole of the modular invariant $j$, so that it is a cusp in the project's sense. It is used throughout the later treatment of $X_0(N)$, for instance in the analysis of charts and residues near the cusp at infinity and in height estimates on the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCusp_cuspInftyBar.lean

import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCusp_cuspInftyBar (N : ℕ) [NeZero N] : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) (cuspInftyBar N) := by sorry
