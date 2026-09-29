-- Prove2me | Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
-- name    : ModularCurve.hasSum_modularUnitSeries_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/d56465a1-e65d-5b62-b228-0badbdd944c2
-- title:
--   q-expansion of Δ(τ)/Δ(Nτ) at the cusp ∞
-- statement:
--   Let $N$ be a positive natural number and let $\tau$ lie in the upper half-plane. Write $u =$ [`ModularCurve.modularUnitSeries N`](def/ModularCurve_ModularUnit.html#L127) for the element $\delta \cdot (\mathrm{qExpand}_{\mathbb Q,N}\,\delta)^{-1}$ of the field $\mathbb Q((q))$ of formal Laurent series over $\mathbb Q$, where $\delta =$ [`ModularCurve.deltaSeries`](def/ModularCurve_ModularUnit.html#L107) is $q$ times the power series `dedekindEtaUnitQ` with its coefficients viewed in $\mathbb Q$, and $\mathrm{qExpand}_{\mathbb Q,N}$ is the substitution $q \mapsto q^N$; thus $u$ is the formal quotient $\Delta(q)/\Delta(q^N)$. The assertion is that the family indexed by $m \in \mathbb Z$ whose $m$-th term is the complex number $u_m \, \mathfrak q^m$, with $u_m \in \mathbb Q$ the $m$-th coefficient of $u$ cast into $\mathbb C$ and $\mathfrak q =$ `Function.Periodic.qParam 1 (τ : ℂ)` $= e^{2\pi i \tau}$ (integer powers being taken in $\mathbb C$), is summable with sum
--   $$\frac{\Delta(\tau)}{\Delta\big(\mathrm{heckeDiagMatrix}(N) \cdot \tau\big)},$$
--   where $\Delta$ is Mathlib's discriminant cusp form and $\mathrm{heckeDiagMatrix}(N)$ is the element $\begin{pmatrix} N & 0 \\ 0 & 1\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb R)$, acting on the upper half-plane by Möbius transformation, so that the denominator is $\Delta(N\tau)$.
--
--   This identifies the formal Laurent series $\Delta(q)/\Delta(q^N)$ with the analytic modular unit $\tau \mapsto \Delta(\tau)/\Delta(N\tau)$ on $X_0(N)$, Ogg's unit, realised at period $1$ at the cusp $\infty$; no primality of $N$ is required. It is the bridge between the formal and analytic descriptions used in the computation of the Fricke involution on this unit and in the descent placing the relevant functions in $\mathbb Q(j, j_N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_modularUnitSeries_qParam.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ)) := by sorry
