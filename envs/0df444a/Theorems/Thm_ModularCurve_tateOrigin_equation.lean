-- Prove2me | Theorems.Thm_ModularCurve_tateOrigin_equation
-- name    : ModularCurve.tateOrigin_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/d1b9d070-0fe0-517c-a865-83149f6dc7c9
-- title:
--   The Tate curve equation for the point at u=1+T
-- statement:
--   Let $K$ be a commutative ring and work in $\mathrm{LaurentSeries}(K[[\mathfrak q]])$, Laurent series in a variable $T$ over the power series ring in $\mathfrak q$. Put $x = \mathtt{tateOriginX}\,K$, the sum of $T^{-2}$, $T^{-1}$ and the series whose $T^k$-coefficient ($k \ge 0$) is the power series in $\mathfrak q$ with $\mathfrak q^0$-coefficient $0$ and $\mathfrak q^M$-coefficient ($M \ge 1$) equal to $\sum_{e \mid M} e\bigl(\binom{e}{k} + (-1)^k\binom{e+k-1}{k}\bigr)$, diminished by $2\sum_{e \mid M} e$ when $k = 0$; and $y = \mathtt{tateOriginY}\,K$, the sum of $-T^{-3}$, $-2T^{-2}$, $-T^{-1}$ and the series whose $T^k$-coefficient has $\mathfrak q^0$-coefficient $0$ and $\mathfrak q^M$-coefficient $\sum_{e \mid M}\bigl(\binom{e}{2}\binom{e}{k} - \binom{e+1}{2}(-1)^k\binom{e+k-1}{k}\bigr)$, augmented by $\sum_{e \mid M} e$ when $k = 0$ (all binomial coefficients taken in $\mathbb N$ and cast to $K$). The assertion is the identity $y^2 + xy = x^3 + a_4 x + a_6$, where $a_4, a_6$ are the $T$-degree-zero Laurent series given by the images in $K[[\mathfrak q]]$ of $\mathtt{tateA4} = -\sum_n \bigl(\sum_{d \mid n} 5d^3\bigr)\mathfrak q^n$ and $\mathtt{tateA6} = -\sum_n \bigl(\sum_{d \mid n} (5d^3+7d^5)/12\bigr)\mathfrak q^n$ under $\mathbb Z \to K$ (the divisions by $12$ being exact in $\mathbb Z$).
--
--   This is the Tate uniformisation identity specialised to the parameter $u = 1+T$, re-read with $T$ as the outer variable and with universal coefficients: the point $(x,y)$ lies on the Tate curve $y^2+xy = x^3+a_4(\mathfrak q)x+a_6(\mathfrak q)$ over $K[[\mathfrak q]]$ for every commutative ring $K$. It is obtained from the corresponding statement for a toric point over a characteristic-zero field, [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation) together with the Weierstrass-equation criterion [`ModularCurve.equation_tateBase_iff`](thm.html#ModularCurve.equation_tateBase_iff), and it feeds the computation of the Hasse invariant in [`WeierstrassCurve.hasseInvariant_tatePowerSeries_map`](thm.html#WeierstrassCurve.hasseInvariant_tatePowerSeries_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tateOrigin_equation.lean

import Mathlib
import Definitions.Def_ModularCurve_TateOrigin
import Definitions.Def_ModularCurve_TateFormal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.tateOrigin_equation (K : Type*) [CommRing K] :
    tateOriginY K ^ 2 + tateOriginX K * tateOriginY K
      = tateOriginX K ^ 3 + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA4) * tateOriginX K
        + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA6) := by sorry
