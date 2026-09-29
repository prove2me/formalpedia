-- Prove2me | Theorems.Thm_ModularCurve_isKummerGenerator_one_hasseRootFn_of_charP_two
-- name    : ModularCurve.isKummerGenerator_one_hasseRootFn_of_charP_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/09c8b693-517f-5b0e-91aa-3389f30767e8
-- title:
--   At p=2 the Hasse root lies in k(X₁(M))
-- statement:
--   Let $M$ be a non-zero natural number with $M \ge 5$ and $2 \nmid M$, and let $k$ be an algebraically closed field of characteristic $2$. Let $w$ be an integral weight-one form of level $M$ over $k$, that is: a modular form `form` of weight $1$ for $\Gamma_1(M)$, viewed as a subgroup of $\mathrm{GL}(2,\mathbb{R})$, together with a power series `series` over $\mathbb{Z}$ whose image under $\mathbb{Z} \to \mathbb{C}$ is the $q$-expansion of `form` with respect to the period $1$, and subject to the requirement that the Laurent series $\mathrm{intSeriesC}\,k\,(\mathtt{series})$ over $k$ — the coefficientwise reduction of `series` to $k$, regarded inside $k((q))$ — is non-zero. The theorem asserts that $w.\mathrm{hasseRootFn} = (\mathrm{intSeriesC}\,k\,w.\mathtt{series})^{-1}$ is a Kummer generator of exponent $1$ for the intermediate field $\mathrm{x1FunctionFieldC}\,k\,M$ of $k((q))$ over $k$, namely the subfield generated over $k$ by the ratios of reductions of integral forms for $\Gamma_1(M)$; concretely: $1 > 0$, the element $(\mathrm{intSeriesC}\,k\,w.\mathtt{series})^{-1}$ is non-zero, and its first power — so the element itself — lies in $\mathrm{x1FunctionFieldC}\,k\,M$.
--
--   This is the characteristic-$2$ case of the statement that the reciprocal of the reduced weight-one form, the root of the Hasse invariant used to build the Igusa cover, generates a Kummer extension of the $q$-expansion function field of $X_1(M)$; here the exponent degenerates to $1$, i.e. the Hasse root already lies in $k(X_1(M))$ and the Igusa cover is trivial at $p = 2$. It feeds the uniform statement [`ModularCurve.isKummerGenerator_hasseRootFn_x1FunctionFieldC`](thm.html#ModularCurve.isKummerGenerator_hasseRootFn_x1FunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isKummerGenerator_one_hasseRootFn_of_charP_two.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.isKummerGenerator_one_hasseRootFn_of_charP_two
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (h2M : ¬ 2 ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k 2]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ModularCurve.IgusaCover.IsKummerGenerator 1 (ModularCurve.x1FunctionFieldC k M) w.hasseRootFn := by sorry
