-- Prove2me | Theorems.Thm_ModularCurve_hasSum_coeff_etaProd_pow
-- name    : ModularCurve.hasSum_coeff_etaProd_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/8fa72f75-b3de-54c5-8b4f-eae1a976a5d5
-- title:
--   Eta product: formal coefficients sum to prod(1-qⁿ⁺¹)ᵃ
-- statement:
--   Let $a$ be a natural number and let $q$ be a complex number with $\|q\| < 1$. Write `etaProd` for the formal power series $\prod'_{n \in \mathbb{N}} (1 - X^{n+1}) \in \mathbb{Z}[[X]]$, the unconditional product taken in the coefficientwise (product) topology on $\mathbb{Z}[[X]]$, and let $c_m \in \mathbb{Z}$ be the coefficient of $X^m$ in the $a$-th power `etaProd ^ a`. The assertion is that the family $m \mapsto c_m q^m$ of complex numbers, with the integers $c_m$ viewed in $\mathbb{C}$, is summable over $m \in \mathbb{N}$ with sum $\bigl(\prod'_{n \in \mathbb{N}} (1 - q^{n+1})\bigr)^{a}$, the infinite product over $n \in \mathbb{N}$ of the complex numbers $1 - q^{n+1}$ raised to the power $a$. The conclusion is phrased as `HasSum`, so it records both summability of the family and the value of its sum; the complex infinite product on the right is Mathlib's `tprod`.
--
--   This is the bridge between the formal Euler product $\prod_{n \ge 1}(1 - X^n)$ in $\mathbb{Z}[[X]]$ and the convergent product $\prod_{n \ge 1}(1 - q^n)$ on the open unit disc which, up to the factor $q^{1/24}$, defines the Dedekind eta function. It is used when $q$-expansions of eta products and of Siegel units are identified with analytic functions and their coefficients shown to be integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_coeff_etaProd_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.hasSum_coeff_etaProd_pow (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by sorry
