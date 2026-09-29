-- Prove2me | Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam
-- name    : ModularCurve.hasSum_smul_modularUnitSeries_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/e3d1ec42-892a-5646-8975-aea50d1a8e12
-- title:
--   q_N-expansion of Ogg's unit at the cusp 0
-- statement:
--   Let $N$ be a nonzero natural number and let $\tau$ lie in the upper half plane. Write $\Delta$ for Mathlib's `ModularForm.discriminant`, $S$ for the matrix $\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ acting as $\tau\mapsto-1/\tau$ (`ModularGroup.S`), and [`ModularForm.heckeDiagMatrix N`](def/ModularForm_HeckeOperator.html#L21) for the element of $\mathrm{GL}_2(\mathbb{R})$ given by $\begin{pmatrix}N&0\\0&1\end{pmatrix}$, whose action sends $\tau$ to $N\tau$. On the formal side, [`ModularCurve.deltaSeries`](def/ModularCurve_ModularUnit.html#L107) is the Laurent series over $\mathbb{Q}$ equal to $q$ times the power series `dedekindEtaUnitQ` (the rational $\eta$-product unit $\prod_{n\ge1}(1-q^n)^{24}$, whose integral form appears in the $q$-expansion of $\Delta$), `deltaSeriesN N` is its image under the substitution $q\mapsto q^{N}$ (`qExpand ℚ N`), and [`ModularCurve.modularUnitSeries N`](def/ModularCurve_ModularUnit.html#L127) is the quotient $\mathrm{deltaSeries}\cdot(\mathrm{deltaSeriesN}\,N)^{-1}$, i.e. $q^{1-N}\prod_{n\ge1}(1-q^{n})^{24}(1-q^{Nn})^{-24}$ in $\mathbb{Q}((q))$. The assertion is that, with $a_m\in\mathbb{Q}$ the $m$-th coefficient ($m\in\mathbb{Z}$) of the rational rescaling $(N^{12})^{-1}\cdot\mathrm{modularUnitSeries}\,N$, the family $m\mapsto a_m\,q_N^{\,m}$, where $q_N=\mathtt{qParam}\,N\,\tau=e^{2\pi i\tau/N}$, is summable with sum $\Delta(N\cdot S\tau)/\Delta(S\tau)$; the convergence statement is `HasSum` over all of $\mathbb{Z}$ and holds for every $\tau$ in the upper half plane.
--
--   This identifies the formal Laurent series $N^{-12}\,\Delta(q)/\Delta(q^{N})$, read in the parameter $q_N=e^{2\pi i\tau/N}$, as the expansion at the cusp $0$ of the modular unit on $X_0(N)$ attached to $\Delta(N\tau)/\Delta(\tau)$ (Ogg's unit), the cusp-$0$ counterpart of its expansion at $\infty$. It feeds the proofs that [`ModularCurve.modularUnitSeries`](def/ModularCurve_ModularUnit.html#L127) lies in the modular function field and that it and its inverse are integral over $\mathbb{Q}[j]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_smul_modularUnitSeries_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((((N : ℚ) ^ 12)⁻¹ • ModularCurve.modularUnitSeries N).coeff m : ℚ) : ℂ) * Function.Periodic.qParam N (τ : ℂ) ^ m) (ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ) / ModularForm.discriminant (ModularGroup.S • τ)) := by sorry
