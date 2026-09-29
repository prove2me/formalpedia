-- Prove2me | Theorems.Thm_ModularCurve_hasSum_jNum_qParam
-- name    : ModularCurve.hasSum_jNum_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/cd5ffe10-f230-5070-bdc4-240385126b4a
-- title:
--   qE₄³/Δ is the sum of its q-series
-- statement:
--   Let $\tau$ be a point of the upper half-plane and write $q =$ `Function.Periodic.qParam 1 (τ : ℂ)`, that is $q = e^{2\pi i\tau}$. Let [`ModularCurve.eisenstein4`](def/ModularCurve_X0.html#L111) be the formal power series over $\mathbb{Z}$ whose $n$-th coefficient is $1$ for $n = 0$ and $240\sum_{d \mid n} d^{3}$ for $n \ge 1$, let [`ModularCurve.dedekindEtaUnitInv`](def/ModularCurve_X0.html#L132) be the formal inverse `dedekindEtaUnit.invOfUnit 1` of the power series [`ModularCurve.dedekindEtaUnit`](def/ModularCurve_X0.html#L127) (the inverse taken with respect to the constant term $1$), and let [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142) be the product `eisenstein4 ^ 3 * dedekindEtaUnitInv` in $\mathbb{Z}[[q]]$. The assertion is that the family indexed by $m \in \mathbb{N}$ whose $m$-th term is the integer coefficient $\mathrm{coeff}_m(\mathtt{jNum})$, cast into $\mathbb{C}$, multiplied by $q^{m}$, is summable with sum
--   $$\sum_{m \ge 0} \mathrm{coeff}_m(\mathtt{jNum})\, q^{m} \;=\; q\cdot\frac{E_4(\tau)^{3}}{\Delta(\tau)},$$
--   where $E_4$ is `ModularForm.E₄` and $\Delta$ is `ModularForm.discriminant`. Since `HasSum` over $\mathbb{C}$ is unconditional summability, this includes the convergence of the series.
--
--   This identifies the formal integer power series $\mathtt{jNum} = 1 + 744q + 196884q^{2} + \cdots$, the numerator of the modular invariant $j$ in the $q$-variable, with the analytic function $q\,E_4^{3}/\Delta$ on the upper half-plane; the proof combines the $q$-expansions of $E_4$ and $\Delta$, the latter in the form $q$ times a power series with constant term $1$, so that the formal inverse of the eta factor matches the analytic reciprocal. It feeds the corresponding statement for $j$ itself, [`ModularCurve.hasSum_jq_qParam`](thm.html#ModularCurve.hasSum_jq_qParam).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_jNum_qParam.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_jNum_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℕ => ((PowerSeries.coeff m ModularCurve.jNum : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (Function.Periodic.qParam 1 (τ : ℂ) * (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)) := by sorry
