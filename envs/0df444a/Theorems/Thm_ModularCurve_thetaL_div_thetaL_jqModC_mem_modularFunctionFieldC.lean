-- Prove2me | Theorems.Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
-- name    : ModularCurve.thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/978388c8-6a5d-5cf7-9d5d-a0ea18dc93b8
-- title:
--   Stability of K(jmath̄,jmath̄_N) under θ/thetajmath̄
-- statement:
--   Let $p$ be a prime, $K$ a field of characteristic $p$, and $N\ge 1$ an integer with $p\nmid N$. Inside the field $K((q))$ of Laurent series over $K$, write $\bar\jmath$ for `jqModC K`, the Laurent series $q^{-1}\cdot\overline{\mathrm{jNum}}$ obtained from the power series $E_4^3\,\eta^{-24}$ (i.e. `jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv`) by reducing its integer coefficients into $K$, and write $\bar\jmath_N$ for `jqNModC K N`, the image of $\bar\jmath$ under the substitution $q\mapsto q^N$. Let `modularFunctionFieldC K N` be the intermediate field $K(\bar\jmath,\bar\jmath_N)$ of $K((q))$ generated over $K$ by these two elements, and let $\theta=$ `thetaL K` be the $K$-linear operator $f\mapsto q\,f'$ on $K((q))$, that is, multiplication by the monomial $q^{1}$ composed with the formal derivative. The assertion is: for every $x\in K((q))$ lying in $K(\bar\jmath,\bar\jmath_N)$, the quotient $\theta x/\theta\bar\jmath$ again lies in $K(\bar\jmath,\bar\jmath_N)$.
--
--   The quotient $\theta/\theta\bar\jmath$ is the derivation "$d/d\bar\jmath$" of $K((q))$, and the statement says that the level-$N$ modular function field in characteristic $p\nmid N$ is stable under it. It is used in the construction and evaluation of the auxiliary modular functions attached to $X_0(N)$ in characteristic $p$, notably by [`ModularCurve.qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC`](thm.html#ModularCurve.qP_mul_thetaL_jqModC_zpow_mem_modularFunctionFieldC) and by the results computing ramification and widths at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (x : LaurentSeries K) (hx : x ∈ modularFunctionFieldC K N) :
    thetaL K x / thetaL K (jqModC K) ∈ modularFunctionFieldC K N := by sorry
