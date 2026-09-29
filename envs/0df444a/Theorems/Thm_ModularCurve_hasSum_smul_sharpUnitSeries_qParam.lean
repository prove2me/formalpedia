-- Prove2me | Theorems.Thm_ModularCurve_hasSum_smul_sharpUnitSeries_qParam
-- name    : ModularCurve.hasSum_smul_sharpUnitSeries_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/31f83f99-a0c3-5d0a-abb1-f38f09808a73
-- title:
--   q-expansion at the cusp 0 of the eta quotient unit
-- statement:
--   Let $\ell$ be a non-zero natural number and let $\tau$ lie in the upper half-plane. Write $i(\ell)=\gcd(\ell-1,12)$ for `sharpIndex ℓ` and $e(\ell)=24/i(\ell)$ for `sharpExp ℓ`, and let $A_\ell=$ `sharpUnitSeries ℓ` be the Laurent series over $\mathbb{Q}$ obtained as $q^{-(\ell-1)/i(\ell)}$ times the image in $\mathbb{Q}[[q]]$ of $(\mathrm{etaProd})^{e(\ell)}$, divided by the series obtained from that same power series by the exponent-rescaling ring homomorphism `qExpand ℚ ℓ` (substitution $q\mapsto q^{\ell}$). The theorem asserts that the family indexed by $m\in\mathbb{Z}$ whose $m$-th term is the complex number $\ell^{-\lfloor e(\ell)/2\rfloor}\,A_\ell(m)$ (the $m$-th coefficient of the scalar multiple $((\ell)^{e(\ell)/2})^{-1}\cdot A_\ell$, with natural-number division in the exponent, cast from $\mathbb{Q}$ to $\mathbb{C}$) times $q_\ell(\tau)^m$, where $q_\ell(\tau)=\exp(2\pi i\tau/\ell)$ is `Function.Periodic.qParam ℓ`, is summable with sum the inverse of `sharpUnitFun ℓ` evaluated at $S\cdot\tau=-1/\tau$, that is, $\bigl(\eta(-1/\tau)/\eta(\ell\cdot(-1/\tau))\bigr)^{-e(\ell)}$, the Hecke matrix $\mathrm{diag}(\ell,1)$ acting by $\tau\mapsto\ell\tau$.
--
--   This is the expansion, in the parameter $q^{1/\ell}=e^{2\pi i\tau/\ell}$, of the reciprocal of the eta quotient modular unit at the cusp $0$, obtained from its expansion at $\infty$ by the Fricke involution; the factor $\ell^{-e(\ell)/2}$ is the one produced by $\eta(-1/\tau)=\sqrt{-i\tau}\,\eta(\tau)$. It is used in showing that `sharpUnitSeries ℓ` is the $q$-expansion of an element of the function field of $X_0(\ell)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_smul_sharpUnitSeries_qParam.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_smul_sharpUnitSeries_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((((ℓ : ℚ) ^ (ModularCurve.sharpExp ℓ / 2))⁻¹ • ModularCurve.sharpUnitSeries ℓ).coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) ((ModularCurve.sharpUnitFun ℓ (ModularGroup.S • τ))⁻¹) := by sorry
