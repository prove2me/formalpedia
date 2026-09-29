-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod
-- name    : ModularCurve.qExpansion_discriminant_eq_X_mul_tprod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/7b620c6f-aea9-5c41-881b-5c8cdb8e88d6
-- title:
--   q-expansion of Δ as a formal product
-- statement:
--   The statement is a closed identity in the ring $\mathbb{C}[[X]]$ of formal power series over $\mathbb{C}$, with no variables or hypotheses. On the left stands `UpperHalfPlane.qExpansion 1 ModularForm.discriminant`: the formal $q$-expansion, with respect to the period $1$, of the modular discriminant $\Delta$ on the upper half-plane, i.e. the power series whose $n$-th coefficient is the $n$-th Taylor coefficient at $q=0$ of the function on the punctured unit disc obtained from $\Delta(\tau)$ by the substitution $q=e^{2\pi i\tau}$. On the right stands the formal power series $X\cdot\prod'_{n\in\mathbb{N}}(1-X^{n+1})^{24}$, where the unordered product $\prod'$ is the unconditional (multipliable) product in `PowerSeries ℂ` taken with respect to the coefficientwise, i.e. $X$-adic, topology supplied by the `PowerSeries.WithPiTopology` scope; the indexing runs over all natural numbers $n\ge 0$, so the factors are $(1-X^{m})^{24}$ for $m\ge 1$. The assertion is that these two power series are equal, that is, $\sum_{n\ge 0}\tau(n)X^{n} = X\prod_{m\ge 1}(1-X^{m})^{24}$.
--
--   This is the classical product formula for the discriminant $\Delta = \eta^{24}$, here in its formal rather than pointwise form: it transfers the analytic identity $\Delta = q\prod_{m\ge1}(1-q^{m})^{24}$ into an identity of formal power series, where the coefficients $\tau(n)$ can be manipulated algebraically. It is used to identify the $q$-expansion of $\Delta$ with the image of $X$ times the Dedekind eta unit, in [`ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`](thm.html#ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean

import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.PowerSeries.PiTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped PowerSeries.WithPiTopology

theorem ModularCurve.qExpansion_discriminant_eq_X_mul_tprod : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.X * ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by sorry
