-- Prove2me | Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam
-- name    : ModularCurve.hasSum_modularUnitSeries_inv_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/e24eecd1-3402-5bd9-9259-9c738c5d3f11
-- title:
--   q-expansion of Δ(Nτ)/Δ(τ) realised at period one
-- statement:
--   Let $N$ be a nonzero natural number and let $\tau$ lie in the upper half-plane. Consider the formal Laurent series over $\mathbb{Q}$ given by [`ModularCurve.modularUnitSeries N`](def/ModularCurve_ModularUnit.html#L127), namely the product of `deltaSeries` $= q\cdot\mathrm{dedekindEtaUnitQ}(q)$ (the Hahn series $q$ times the power series [`ModularCurve.dedekindEtaUnitQ`](def/ModularCurve_ModularUnit.html#L99)) with the inverse of its $N$-fold $q$-substitution `deltaSeriesN N` $=$ `qExpand ℚ N deltaSeries`; informally $\Delta(q)/\Delta(q^{N})$. The assertion concerns the inverse of this series in the field of formal Laurent series over $\mathbb{Q}$, whose $m$-th coefficients $v_m$ are rational numbers, viewed in $\mathbb{C}$. The conclusion is that the family indexed by $m \in \mathbb{Z}$ whose $m$-th term is $v_m\,q^{m}$, where $q =$ `Function.Periodic.qParam 1 τ` $= e^{2\pi i \tau}$ and $q^m$ is the integral power, is summable with sum equal to the quotient of Mathlib's discriminant modular form `ModularForm.discriminant` evaluated at [`ModularForm.heckeDiagMatrix N • τ`](def/ModularForm_HeckeOperator.html#L21) — the Möbius action on $\tau$ of the upper triangular matrix $\begin{pmatrix} N & 0\\ 0 & 1\end{pmatrix}$, i.e. at $N\tau$ — by its value at $\tau$. Thus $\sum_{m \in \mathbb{Z}} v_m e^{2\pi i m \tau} = \Delta(N\tau)/\Delta(\tau)$, as an unconditional `HasSum` statement valid at every point of the upper half-plane.
--
--   This identifies the analytic function realised at period $1$ by the inverse of the modular unit series, namely the $q$-expansion at $\infty$ of $\Delta(N\tau)/\Delta(\tau)$, the reciprocal of Ogg's unit on $X_0(N)$. It is used in the proofs that both the modular unit series and its inverse are integral over $\mathbb{Q}[j]$, and in the descent of the $q$-expansion of the relevant product to $\mathbb{Q}(j, j_N)$; the corresponding statement for $1/F$ does not follow formally from the one for $F$, whence the separate result.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) / ModularForm.discriminant τ) := by sorry
