-- Prove2me | Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn
-- name    : ModularCurve.isKummerGenerator_hasseRootFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c00a0ae9-d60f-586a-808c-afa5266c1eb5
-- title:
--   The Hasse root function generates a Kummer extension of exponent p-1
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $\kappa$ be a field of characteristic $p$, and let $M$ be a non-zero natural number. Let $w$ be an integral weight-one form of level $M$ over $\kappa$, that is: a modular form `w.form` of weight $1$ for $\Gamma_1(M)$ (viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$), a power series `w.series` over $\mathbb{Z}$ whose image under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of `w.form` with respect to the period $1$, and the requirement that $\mathrm{intSeriesC}\ \kappa\ (w.series)$ — the Laurent series over $\kappa$ obtained by reducing the coefficients of `w.series` along $\mathbb{Z} \to \kappa$ and regarding the resulting power series in $\kappa((q))$ — be non-zero. Put $a := w.\mathrm{hasseRootFn} = (\mathrm{intSeriesC}\ \kappa\ (w.series))^{-1} \in \kappa((q))$. The conclusion is the three-part assertion `IsKummerGenerator (p-1) (x1FunctionFieldC κ M) a`: the natural number $p-1$ is positive, $a \neq 0$, and $a^{\,p-1}$ lies in the intermediate field $\mathrm{x1FunctionFieldC}\ \kappa\ M$ of $\kappa((q))$, namely the subfield generated over $\kappa$ by the set `intFormRatiosC κ (Gamma1 M)`.
--
--   This is the Kummer-generator property of the inverse Hasse invariant in characteristic $p$: the $(p-1)$-st power of the reduced inverse of a weight-one $q$-expansion already lies in the $q$-expansion function field of $X_1(M)$ over $\kappa$. It is the first conjunct of the statement that the Igusa function field obtained by adjoining this element is a Kummer extension of degree $p-1$, and is cited by the results computing the relative degree and separability of that extension and by the construction of the associated character of its unit group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isKummerGenerator_hasseRootFn.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.isKummerGenerator_hasseRootFn
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (κ : Type) [Field κ] [CharP κ p]
    (M : ℕ) [NeZero M] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.IgusaCover.IsKummerGenerator (p - 1) (ModularCurve.x1FunctionFieldC κ M) w.hasseRootFn := by sorry
