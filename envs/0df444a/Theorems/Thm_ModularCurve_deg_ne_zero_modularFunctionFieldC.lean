-- Prove2me | Theorems.Thm_ModularCurve_deg_ne_zero_modularFunctionFieldC
-- name    : ModularCurve.deg_ne_zero_modularFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/86203315-985f-5ea0-9330-962da2bfe134
-- title:
--   Places of K(j,j_N) have nonzero degree
-- statement:
--   Let $K$ be a field (arbitrary characteristic) and let $N$ be a natural number with $N \neq 0$. Inside the field $\mathrm{LaurentSeries}\ K$ of Laurent series over $K$, write $j$ for `jqModC K`, the series $q^{-1}$ times the image under $K$-coefficient reduction of the integral power series `jNum`, and $j_N$ for `jqNModC K N`, obtained from $j$ by the substitution `qExpand K N` (raising the variable to the $N$-th power); let `modularFunctionFieldC K N` be the intermediate field $K(j,j_N)$ of $\mathrm{LaurentSeries}\ K$ generated over $K$ by these two elements. Let $w$ be a place of $K(j,j_N)$ over $K$ in the sense of the project's structure `Place`, that is, a valuation subring of $K(j,j_N)$ which contains the image of $K$, is not the whole field, and is a principal ideal ring. The conclusion is that $w.\mathrm{deg} \neq 0$, where $w.\mathrm{deg}$ is the $K$-dimension $\operatorname{finrank}_K$ of the residue field of that valuation subring; equivalently, the residue field of $w$ is a finite extension of $K$.
--
--   This is the statement that the level-$N$ modular function field, realised concretely as the subfield $K(j,j_N)$ of $K((q))$, is a function field over $K$ in the sense that all its places have finite residue degree. It is used in the construction of places of this field from solutions of the modular polynomial and in the verifications that the modular function field and its base changes are curves over the relevant base fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_ne_zero_modularFunctionFieldC.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.deg_ne_zero_modularFunctionFieldC (K : Type*) [Field K] (N : ℕ) [NeZero N] (w : Place K (modularFunctionFieldC K N)) : w.deg ≠ 0 := by sorry
