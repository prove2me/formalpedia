-- Prove2me | Theorems.Thm_ModularCurve_legendreJ_one_sub
-- name    : ModularCurve.legendreJ_one_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/404838b7-1780-53ee-9b77-8c6fb77e49e2
-- title:
--   Invariance of the Legendre j-map under t ↦ 1-t
-- statement:
--   Let $K$ be a field and let $t \in K$ be arbitrary. Write $\mathrm{legendreJ}(t) = 2^{8}(t^{2}-t+1)^{3}/\bigl(t^{2}(t-1)^{2}\bigr)$, the quotient being formed in $K$ with Lean's total division, so that the value is $0$ whenever the denominator vanishes. The theorem asserts the equality $\mathrm{legendreJ}(1-t) = \mathrm{legendreJ}(t)$ in $K$. No restriction is placed on $t$: the identity is stated for every element of every field, including the degenerate values $t = 0$ and $t = 1$, where $t^{2}(t-1)^{2} = 0$ and both sides are $0$ by the division convention, and including fields of arbitrary characteristic. The substance of the identity is that both the numerator factor $t^{2}-t+1$ and the denominator $t^{2}(t-1)^{2}$ are unchanged when $t$ is replaced by $1-t$.
--
--   This is one of the two generating symmetries of the classical Legendre $\lambda$-line over the $j$-line, expressing that the modular invariant of the Legendre curve with parameter $\lambda$ depends only on the orbit of $\lambda$ under the anharmonic group. It feeds into [`ModularCurve.legendreJ_eq_legendreJ_iff`](thm.html#ModularCurve.legendreJ_eq_legendreJ_iff), the description of when two parameters give the same $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_legendreJ_one_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.legendreJ_one_sub {K : Type*} [Field K] (t : K) : legendreJ (1 - t) = legendreJ t := by sorry
