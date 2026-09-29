-- Prove2me | Theorems.Thm_ModularCurve_modularFunctionFieldFullC_one
-- name    : ModularCurve.modularFunctionFieldFullC_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/b9662ac0-82a0-5fa7-86f2-c77ca2ea870b
-- title:
--   At level one the all-divisors modular function field is K(j(q))
-- statement:
--   Let $K$ be a field. Inside the field of formal Laurent series $K(\!(q)\!)$ consider the Laurent series $j(q) =$ `jqModC K`, namely $q^{-1}$ times the image under $\mathbb{Z} \to K$ of the integral power series `jNum`, so that $j(q) = q^{-1} + \dots$ is the $q$-expansion of the modular invariant with coefficients read in $K$. Two intermediate fields of $K(\!(q)\!)/K$ are compared at level $N = 1$: the all-divisors field `modularFunctionFieldFullC K 1`, the subfield of $K(\!(q)\!)$ generated over $K$ by the set of all substitutions $q \mapsto q^d$ applied to $j(q)$, for $d$ a nonzero natural number dividing $1$; and the two-generator field `modularFunctionFieldC K 1`, generated over $K$ by $j(q)$ together with its substitution $q \mapsto q^{1}$. The theorem asserts that these two intermediate fields of $K(\!(q)\!)$ are equal. No hypothesis beyond $K$ being a field is imposed; in particular there is no restriction on the characteristic.
--
--   This identifies, at level one, the presentation of the modular function field by all divisor substitutions $j(q^d)$, $d \mid N$, with the two-generator presentation $K(j(q), j(q^N))$ of the function field whose degree-zero divisor classes model $J_0(N)$. It is used in the analysis of places and prolongations on the level-one fibre (the $j$-line), where arguments must pass freely between the two presentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularFunctionFieldFullC_one.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.modularFunctionFieldFullC_one (K : Type*) [Field K] :
    modularFunctionFieldFullC K 1 = modularFunctionFieldC K 1 := by sorry
