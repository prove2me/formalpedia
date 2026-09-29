-- Prove2me | Theorems.Thm_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
-- name    : ModularCurve.six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8706628d-947c-5a96-b90f-79c47a44ec27
-- title:
--   Ogg's unit has order zero at affine places
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $N \ge 1$ with $p \nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Inside the Laurent series field $K((q))$ consider $\tilde\jmath =$ `jqModC K`, the series $q^{-1}\cdot(E_4^3\eta^{-24})$ obtained by reducing the integral $q$-expansion of $j$, and $\tilde\jmath_N =$ `jqNModC K N`, its image under the substitution $q \mapsto q^N$; let $F =$ `modularFunctionFieldC K N` be the intermediate field $K(\tilde\jmath, \tilde\jmath_N)$ they generate. Let $\theta =$ `thetaL K` be the $K$-linear operator $q\,d/dq$ on $K((q))$, and let $h \in F$ satisfy $h \cdot \theta\tilde\jmath = \theta\tilde\jmath_N$ as Laurent series. Let $w$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, and assume $w$ is affine in the sense that both $\tilde\jmath$ and $\tilde\jmath_N$ lie in its valuation subring. Then, with $\operatorname{ord}_w$ the normalised valuation attached to $w$, $$6\operatorname{ord}_w h + 4\operatorname{ord}_w \tilde\jmath + 3\operatorname{ord}_w(\tilde\jmath - 1728) = 4\operatorname{ord}_w \tilde\jmath_N + 3\operatorname{ord}_w(\tilde\jmath_N - 1728),$$ where $1728$ denotes its image in $F$ under the structure map from $K$.
--
--   Via the identity $(\theta j)^6 = j^4(j-1728)^3\Delta$ and $\theta(j(q^N)) = N\,(\theta j)(q^N)$, the asserted equality of orders says precisely that Ogg's modular unit $\Delta(q)/\Delta(q^N)$ has order zero at every place of the level-$N$ modular function field in characteristic $p \ge 5$ at which both $\tilde\jmath$ and $\tilde\jmath_N$ are regular, i.e. that the divisor of the eta-quotient is supported on the cusps. It feeds the computation of ramification of the $j$-map on $X_0(N)$ in characteristic $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.six_mul_ord_add_eq_of_coe_mul_thetaL_jqModC_eq_thetaL_jqNModC_of_isAffineGeomPlace
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (h : ↥(modularFunctionFieldC K N))
    (hh : (h : LaurentSeries K) * thetaL K (jqModC K) = thetaL K (jqNModC K N))
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : IsAffineGeomPlace K N w) :
    6 * w.ord h + 4 * w.ord (jGeomGen K N)
        + 3 * w.ord (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728)
      = 4 * w.ord (jNGeomGen K N)
        + 3 * w.ord (jNGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) 1728) := by sorry
