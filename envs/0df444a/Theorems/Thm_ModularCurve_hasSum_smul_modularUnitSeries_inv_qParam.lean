-- Prove2me | Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
-- name    : ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/8d6b4a79-8c6a-527a-a302-f2da8aa65ed2
-- title:
--   q-expansion of Ogg's unit at the cusp 0
-- statement:
--   Let $N$ be a non-zero natural number and let $\tau$ lie in the upper half plane $\mathfrak H$. Consider the formal Laurent series over $\mathbb Q$ (Hahn series with value group $\mathbb Z$) given by [`ModularCurve.modularUnitSeries N`](def/ModularCurve_ModularUnit.html#L127) $=$ `deltaSeries` $\cdot$ `deltaSeriesN N`$^{-1}$, where `deltaSeries` is $q$ times the power series `dedekindEtaUnitQ` — that is, the $q$-expansion $q\prod_{n\ge1}(1-q^n)^{24}$ of the discriminant form, the integral model of whose unit factor satisfies [`ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`](thm.html#ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit) — and `deltaSeriesN N` is its image under $q\mapsto q^N$ (`qExpand`); thus `modularUnitSeries N` $=\Delta(q)/\Delta(q^N)$. The theorem asserts that, for the Laurent series $N^{12}\cdot(\mathtt{modularUnitSeries }N)^{-1}$, with the scalar $N^{12}\in\mathbb Q$ acting coefficientwise and the inverse taken in the field of formal Laurent series, the family indexed by $m\in\mathbb Z$ whose $m$-th term is the complex image of the $m$-th coefficient multiplied by $q_N(\tau)^m$, where $q_N(\tau)=$ `Function.Periodic.qParam N` $(\tau)=e^{2\pi i\tau/N}$, is summable with sum
--   $$\frac{\Delta(S\tau)}{\Delta(N\,S\tau)},$$
--   where $\Delta$ is `ModularForm.discriminant`, $S$ is the standard element of the modular group acting by $\tau\mapsto-1/\tau$, and multiplication by $N$ is the action of [`ModularForm.heckeDiagMatrix N`](def/ModularForm_HeckeOperator.html#L21), the matrix $\begin{pmatrix}N&0\\0&1\end{pmatrix}$. Summability is unconditional over all integers $m$ and is asserted for every $\tau$, with no primality assumption on $N$.
--
--   This identifies the $q$-expansion, in the local parameter $e^{2\pi i\tau/N}$ at the width-$N$ cusp $0$, of Ogg's modular unit $\Delta(\tau)/\Delta(N\tau)$ on $X_0(N)$, the factor $N^{12}$ arising from applying $\Delta(-1/\tau)=\tau^{12}\Delta(\tau)$ at the two arguments. It feeds the computation of the Fricke involution on the unit ([`ModularCurve.coe_frickeInvolutionFull_modularUnitSeries`](thm.html#ModularCurve.coe_frickeInvolutionFull_modularUnitSeries) and its variant under a non-vanishing hypothesis) and the integrality of the unit over $\mathbb Q[j]$ ([`ModularCurve.isIntegral_adjoin_jq_modularUnitSeries`](thm.html#ModularCurve.isIntegral_adjoin_jq_modularUnitSeries)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam (N : ℕ) [NeZero N] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((N : ℚ) ^ 12 • (ModularCurve.modularUnitSeries N)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam N (τ : ℂ) ^ m) (ModularForm.discriminant (ModularGroup.S • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • ModularGroup.S • τ)) := by sorry
