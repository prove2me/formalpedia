-- Prove2me | Theorems.Thm_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam
-- name    : ModularCurve.hasSum_smul_sharpUnitSeries_inv_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/bae0795c-7d8e-5bdf-9fc9-84d60e3b0890
-- title:
--   q-expansion at the cusp 0 of the sharp eta quotient
-- statement:
--   Let $\ell$ be a nonzero natural number and let $\tau$ lie in the upper half-plane. Write $e=\mathrm{sharpExp}\,\ell=24/\gcd(\ell-1,12)$ (natural-number division, with $\gcd(\ell-1,12)=\mathrm{sharpIndex}\,\ell$), and let $\mathrm{sharpUnitSeries}\,\ell$ be the Laurent series over $\mathbb{Q}$ given by the product of the monomial $q^{-(\ell-1)/\gcd(\ell-1,12)}$, the power series $\prod$-expansion $\mathrm{etaProd}^{e}$ pushed to $\mathbb{Q}$, and the inverse of the image of that same power series under the substitution $q\mapsto q^{\ell}$ (the ring homomorphism `qExpand` scaling exponents by $\ell$). The assertion is that the family indexed by $m\in\mathbb{Z}$ whose $m$-th term is the complex number obtained from the $m$-th coefficient of the Laurent series $\ell^{\lfloor e/2\rfloor}\cdot(\mathrm{sharpUnitSeries}\,\ell)^{-1}$ (inverse in the field of Laurent series over $\mathbb{Q}$, scaled by the rational $(\ell)^{e/2}$ with $e/2$ again natural division) multiplied by $\mathrm{qParam}\,\ell(\tau)^{m}=e^{2\pi i m\tau/\ell}$ is summable with sum $\mathrm{sharpUnitFun}\,\ell(S\cdot\tau)$, where $S\in\mathrm{SL}_2(\mathbb{Z})$ is the standard involution $\tau\mapsto-1/\tau$ and $\mathrm{sharpUnitFun}\,\ell(\sigma)=\bigl(\eta(\sigma)/\eta(\ell\sigma)\bigr)^{e}$, the second argument being the action of the diagonal matrix `heckeDiagMatrix ℓ`.
--
--   This is the expansion of the eta quotient $(\eta(\tau)/\eta(\ell\tau))^{e}$ at the cusp $0$, obtained from its expansion at $\infty$ by the transformation $\tau\mapsto-1/\tau$, and expressed in the local parameter $q_\ell=e^{2\pi i\tau/\ell}$ there; the constant $\ell^{e/2}$ records the even-power form of the transformation law for $\eta$, so that no square root has to be chosen. It is used to show that `sharpUnitSeries` belongs to the field of modular functions, in [`ModularCurve.sharpUnitSeries_mem_modularFunctionField`](thm.html#ModularCurve.sharpUnitSeries_mem_modularFunctionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_smul_sharpUnitSeries_inv_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ℓ : ℚ) ^ (ModularCurve.sharpExp ℓ / 2) • (ModularCurve.sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (ModularCurve.sharpUnitFun ℓ (ModularGroup.S • τ)) := by sorry
