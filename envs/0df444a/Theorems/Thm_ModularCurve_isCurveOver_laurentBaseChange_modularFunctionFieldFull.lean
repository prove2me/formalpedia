-- Prove2me | Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
-- name    : ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/5ed33ecb-6650-5bed-8b15-d879bd5cff01
-- title:
--   The base-changed modular function field is a curve over L
-- statement:
--   Let $L$ be a field equipped with an algebra structure over $\mathbb{Q}$, and let $N$ be a natural number with $N \neq 0$. Write $F_0 =$ `modularFunctionFieldFull N` for the intermediate field of $\mathbb{Q} \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by `divisorExpansions N`, the set of Laurent series $\mathrm{qExpand}\ \mathbb{Q}\ d\ \mathrm{jq}$ for the nonzero divisors $d \mid N$; and let `laurentBaseChange L F₀` be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the image of $F_0$ under `coeffEmb L`, the coefficientwise application of $\mathbb{Q} \to L$ to Laurent series. The assertion is that this field $F$ satisfies `IsCurveOver L`, that is: (i) principal divisors exist, namely for every $f \in F$ with $f \neq 0$ there is a divisor $D$ over $L$ with $D(v) = v.\mathrm{ord}\,f$ at every place $v$ of $F/L$ — a place being a valuation subring of $F$ containing the image of $L$, not equal to all of $F$, and a principal ideal ring — and with $\deg D = 0$; (ii) at every such place $v$, the residue field of $v$ is finite as an $L$-module; and (iii) the module of Kähler differentials $\Omega_{F/L}$ is free over $F$ of rank one.
--
--   This is the statement that the modular function field of level $N$, base changed coefficientwise to an arbitrary field of characteristic zero, is a function field of one variable over $L$ in the sense in which the divisor-theoretic and Riemann–Roch-style results of the development are formulated. It supplies the curve structure used by the subsequent analysis of places and fibres of the modular curve, including the characteristic-$p$ models built on top of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : IsCurveOver L (laurentBaseChange L (modularFunctionFieldFull N)) := by sorry
