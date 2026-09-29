-- Prove2me | Theorems.Thm_IsNonarchimedean_apply_le_one_of_isIntegral_int
-- name    : IsNonarchimedean.apply_le_one_of_isIntegral_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/46027c84-3d84-5afa-baca-d0b85a4ff0d9
-- title:
--   Elements integral over ℤ have non-archimedean absolute value ≤ 1
-- statement:
--   Let $K$ be a field and let $\mu : K \to \mathbb{R}$ be an absolute value on $K$ (in the Mathlib sense: multiplicative, non-negative, vanishing only at $0$, and subadditive). Assume $\mu$ is non-archimedean, i.e. $\mu(a+b) \le \max(\mu a, \mu b)$ for all $a, b \in K$. Let $x \in K$ be integral over $\mathbb{Z}$, that is, there is a monic polynomial $p \in \mathbb{Z}[X]$ with $p(x) = 0$ under the ring map $\mathbb{Z} \to K$. The conclusion is $\mu(x) \le 1$. No completeness, discreteness or residual hypothesis on $\mu$ is imposed, and $K$ is arbitrary (in particular no characteristic assumption); the statement is exactly the assertion that every element of $K$ integral over $\mathbb{Z}$ lies in the valuation ring $\{y : \mu(y) \le 1\}$ attached to $\mu$.
--
--   This is the standard fact from valuation theory that elements integral over $\mathbb{Z}$ lie in the valuation ring of any non-archimedean absolute value. It is used in [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot), where it supports uniform bounds on $\log \mu(x)$ for fixed algebraic data in terms of $-\log \mu(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNonarchimedean_apply_le_one_of_isIntegral_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsNonarchimedean.apply_le_one_of_isIntegral_int
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {x : K} (hx : IsIntegral ℤ x) : μ x ≤ 1 := by sorry
