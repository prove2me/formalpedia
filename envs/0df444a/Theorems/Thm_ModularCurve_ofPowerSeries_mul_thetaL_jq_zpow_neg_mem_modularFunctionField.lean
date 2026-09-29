-- Prove2me | Theorems.Thm_ModularCurve_ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField
-- name    : ModularCurve.ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/84937a7a-f895-517a-9867-a14dc8fea754
-- title:
--   Integral even-weight forms divided by (θ j)^m lie in ℚ(j,j_N)
-- statement:
--   Let $N\ge 1$ and let $m$ be a natural number, and let $f$ be a modular form of weight $2m$ (as an integer, $2\cdot(m:\mathbb{Z})$) for the congruence subgroup $\Gamma_0(N)$. Suppose given a sequence $a:\mathbb{N}\to\mathbb{Z}$ of integers such that for every $n$ the $n$-th coefficient of the $q$-expansion of $f$ of width $1$, i.e. [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), equals the complex number $a_n$; thus $f=\sum_{n\ge 0}a_nq^n$ with integral coefficients. Form inside the field $\mathbb{Q}((q))$ of Laurent series (realised as Hahn series over $\mathbb{Z}$) the product of the image of the power series $\sum_{n\ge 0}a_nq^n\in\mathbb{Q}[[q]]$ under `HahnSeries.ofPowerSeries` with the $(-m)$-th integer power of `thetaL ℚ jq`, where `jq` is $q^{-1}$ times the rational power series `jNumQ` (the $q$-expansion of the modular invariant $j$) and `thetaL ℚ` is the $\mathbb{Q}$-linear operator $q\,d/dq$, multiplication by $q$ composed with the derivative of Laurent series. The assertion is that this element lies in `modularFunctionField N`, the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the two elements `jq` and `qExpand ℚ N jq`, the latter being `jq` with its exponents multiplied by $N$, i.e. $j(q^N)$.
--
--   This is the statement that an even-weight modular form on $\Gamma_0(N)$ with rational-integral Fourier coefficients, divided by $(\theta j)^{m}$ — so that the quotient is a modular function of level $N$ with rational coefficients — is a rational function of $j(q)$ and $j(q^N)$, the function field of $X_0(N)$ over $\mathbb{Q}$. It is used in the treatment of mod $p$ modular forms, to produce $q$-expansions of forms of given weight from elements of the relevant mod $p$ modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane ModularCurve

theorem ModularCurve.ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField
    (N : ℕ) [NeZero N] (m : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)))
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (a n : ℚ)) * thetaL ℚ jq ^ (-(m : ℤ)) ∈
      modularFunctionField N := by sorry
