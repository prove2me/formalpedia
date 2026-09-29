-- Prove2me | Theorems.Thm_ModularCurve_c4_tateLaurent
-- name    : ModularCurve.c4_tateLaurent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/f910a8de-500c-5fd0-acf5-f9e6bb590e44
-- title:
--   c₄ of the Tate curve is E₄
-- statement:
--   Let $K$ be a commutative ring. Consider the Weierstrass curve `tatePowerSeries` over the power series ring $\mathbb{Z}[[q]]$ with invariants $a_1 = 1$, $a_2 = a_3 = 0$, $a_4 =$ `tateA4` and $a_6 =$ `tateA6`, and let `tateLaurent K` be its base change along the ring homomorphism `laurentOfInt K` from $\mathbb{Z}[[q]]$ to the field of formal Laurent series over $K$, namely coefficientwise reduction along $\mathbb{Z} \to K$ followed by the inclusion of power series into Laurent series. The theorem asserts that the invariant $c_4 = b_2^2 - 24 b_4$ of this curve over `LaurentSeries K` is the Laurent series obtained from `eisenstein4` by the same two operations, where `eisenstein4` is the power series over $\mathbb{Z}$ whose $0$th coefficient is $1$ and whose $n$th coefficient for $n \neq 0$ is $240 \sum_{d \mid n} d^3$; that is, $c_4$ of the Tate curve over $K$ is the $q$-expansion of $E_4$ with coefficients reduced into $K$.
--
--   This is the classical identity $c_4 = E_4(q)$ for the Tate curve $y^2 + xy = x^3 + a_4(q)x + a_6(q)$, here in the universal form over an arbitrary coefficient ring. It feeds the companion computation of $\Delta$ for the same curve and the construction of $q$-expansions of forms at the cusps, and is used by [`ModularCurve.delta_tateLaurent`](thm.html#ModularCurve.delta_tateLaurent), by the existence statement for $q$-expansions on $\Gamma_H$-curves, and by the evaluation of Katz $\Gamma_0$-forms at cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_c4_tateLaurent.lean

import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve
open PowerSeries HahnSeries in

theorem ModularCurve.c4_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by sorry
