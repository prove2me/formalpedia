-- Prove2me | Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
-- name    : ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/bc1a641e-f351-584e-afb3-91aec20d3c04
-- title:
--   Principal divisors on the level-N modular function field
-- statement:
--   Let $K$ be a perfect field of arbitrary characteristic and let $N$ be a nonzero natural number. Inside the Laurent series field $K((q))$ consider the series $j_q = q^{-1}\cdot\overline{\mathrm{jNum}}$, the reduction to $K$ of the integral power series `jNum` multiplied by $q^{-1}$, and its substitution $j_{q,N}$ obtained by replacing $q$ by $q^N$; let $F$ be `modularFunctionFieldC K N`, the intermediate field $K(j_q, j_{q,N})$ of $K((q))$ generated over $K$ by these two elements. The theorem asserts `HasPrincipalDivisors K F`: for every nonzero $f \in F$ there is a finitely supported function $D$ from the places of $F$ over $K$ to $\mathbb{Z}$ such that $D(v) = \operatorname{ord}_v(f)$ for every place $v$, and $\sum_v D(v)\,\deg v = 0$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Thus each nonzero element of $F$ has only finitely many zeros and poles, and its divisor has degree zero.
--
--   This is the degree-zero theorem for principal divisors, here for the $q$-expansion model $K(j(q), j(q^N))$ of the level-$N$ modular function field over an arbitrary perfect coefficient field, notably $\overline{\mathbb{F}}_p$. It underlies the divisor-theoretic bookkeeping used in the study of places of modular function fields and their prolongations, and is invoked by the specialisation and level-structure arguments built on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.FieldTheory.Perfect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (K : Type*) [Field K] [PerfectField K]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors K (modularFunctionFieldC K N) := by sorry
