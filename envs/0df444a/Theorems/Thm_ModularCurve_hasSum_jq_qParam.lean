-- Prove2me | Theorems.Thm_ModularCurve_hasSum_jq_qParam
-- name    : ModularCurve.hasSum_jq_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9f608b0d-9ccf-5c4d-ab82-4ee1d23f0ee0
-- title:
--   Formal q-series j(q) sums to E₄³/Δ
-- statement:
--   Let $\tau$ be a point of the upper half-plane, and let $q = \mathbb{q}(1,\tau) = e^{2\pi i \tau}$ be the value of Mathlib's $q$-parameter `Function.Periodic.qParam` with period $1$ at $\tau$. Consider the family indexed by $m \in \mathbb{Z}$ whose $m$-th term is the image in $\mathbb{C}$ of the rational number `ModularCurve.jq.coeff m`, the $m$-th coefficient of the formal Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) over $\mathbb{Q}$, multiplied by the integer power $q^{m}$. The assertion is that this family is unconditionally summable over $\mathbb{Z}$, in the sense of `HasSum`, with sum $E_4(\tau)^3 / \Delta(\tau)$, where $E_4$ is Mathlib's normalised weight-$4$ Eisenstein series `ModularForm.E₄` and $\Delta$ is the modular discriminant `ModularForm.discriminant` for $\mathrm{SL}_2(\mathbb{Z})$. Thus the coefficients of the formal series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) are exactly the $q$-expansion coefficients of the analytic modular function $E_4^3/\Delta$ at $\tau$; only the indices $m \ge -1$ contribute, the coefficients of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) in degrees below $-1$ being zero.
--
--   This is the identification of the formal $q$-series used to define the function field of level one with the classical analytic $j$-invariant in the normalisation $j = E_4^3/\Delta$, and so serves as the bridge between the purely formal ($q$-series) construction of $X_0(N)$ and modular polynomials and the analytic theory of modular functions. It is used by the results on hyperplane sections and secant values attached to the divisor of $j$ and by the computation of coefficients of coset polynomials in the `PhiGen` development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_jq_qParam.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_jq_qParam (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((ModularCurve.jq.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by sorry
