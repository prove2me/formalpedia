-- Prove2me | Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
-- name    : ModularCurve.heckeDiamondInputsHAll
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/6da4db63-3f58-560b-b808-48782355d4ab
-- title:
--   Hecke and diamond inputs for the q-expansion model of X_H(M)
-- statement:
--   For every natural number $M \neq 0$ and every subgroup $H \le (\mathbb{Z}/M)^\times$, the predicate [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113) holds, that is, both of the following. (i) For every prime $\ell$, `HeckeInputsHAlong` holds over $L = \overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$) for the data $M$, $H$, $\ell$: there are proofs of `HeckeBetaHDefined M H ℓ`, of `HeckeAlphaHBarIntegral` and `HeckeBetaHBarIntegral` over $\overline{\mathbb{Q}}$, of `HasPrincipalDivisors` for the base change `laurentBaseChange` to $\overline{\mathbb{Q}}$ of the function field `xHTopFunctionFieldC ℚ M H (M * ℓ)`, and of `FiniteAlong` for the map `heckeAlphaHBar`, together with `FundamentalIdentityAlong` for `heckeBetaHBar` (relative to the integrality witness) and `NormFormulaAlong` for `heckeAlphaHBar` (relative to the finiteness witness). (ii) For every $d \in (\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of `xHFunctionFieldBar M H`, the compositum of $\overline{\mathbb{Q}}$ with `xHFunctionField M H` inside $\overline{\mathbb{Q}}((q))$, satisfying `IsDiamondAutHBar M H d σ`: for every weight $k \in \mathbb{Z}$, all modular forms $f, g$ of weight $k$ on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), all integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of $f$ and $g$ with the associated Laurent series `intSeriesC ℚ pg` nonzero, and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$ with upper-left entry congruent to $d$ modulo $M$, there is $y$ in `xHFunctionField M H` such that $\sigma$ sends the element of `xHFunctionFieldBar M H` given by the ratio `intSeriesC ℚ pf / intSeriesC ℚ pg` to the image of $y$ under `coeffEmb`, and such that, after pushing the coefficients of $y$ along $\mathbb{Q} \hookrightarrow \mathbb{C}$, one has $y \cdot (g \mid_k \gamma)^{\wedge} = (f \mid_k \gamma)^{\wedge}$ as $q$-expansions at $\infty$ with complex coefficients.
--
--   This is the unconditional verification of the hypotheses guarding the total definitions of the Hecke correspondences $T_\ell$, $U_q$ and the diamond operators $\langle d \rangle$ on the $q$-expansion model of $X_H(M)$, whose function field is generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of equal weight on $\Gamma_H(M)$. It is invoked throughout the construction of the Galois action and Hecke action on the Jacobian $J_H(M)$ and on its Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDiamondInputsHAll.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeDiamondInputsHAll (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.HeckeDiamondInputsHAll M H := by sorry
