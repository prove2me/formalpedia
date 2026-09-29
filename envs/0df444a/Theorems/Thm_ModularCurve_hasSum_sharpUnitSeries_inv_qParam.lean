-- Prove2me | Theorems.Thm_ModularCurve_hasSum_sharpUnitSeries_inv_qParam
-- name    : ModularCurve.hasSum_sharpUnitSeries_inv_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/6a2c2563-8766-5a4d-82b3-b0ef990d9ced
-- title:
--   q-expansion of the reciprocal eta quotient 1/G_ℓ
-- statement:
--   Let $\ell$ be a nonzero natural number and $\tau$ a point of the upper half-plane. Write $e(\ell) = (\ell-1)/\gcd(\ell-1,12)$ for `eisensteinNumerator ℓ`, $k(\ell) = 24/\,$`sharpIndex ℓ` for `sharpExp ℓ`, and $\Phi_\ell \in \mathbb{Q}[[q]]$ for `etaProdPow ℓ`, the $k(\ell)$-th power of the integral power series `etaProd` pushed forward to $\mathbb{Q}$. Then `sharpUnitSeries ℓ` is the Laurent series $q^{-e(\ell)}\,\Phi_\ell(q)\,\Phi_\ell(q^{\ell})^{-1}$, the substitution $q \mapsto q^{\ell}$ being the ring homomorphism `qExpand ℚ ℓ` that multiplies all exponents by $\ell$, and `sharpUnitFun ℓ τ` is $\bigl(\eta(\tau)/\eta(\mathrm{diag}(\ell,1)\cdot\tau)\bigr)^{k(\ell)}$, with $\mathrm{diag}(\ell,1) =$ `heckeDiagMatrix ℓ` acting on the upper half-plane. The assertion is that the doubly infinite family indexed by $m \in \mathbb{Z}$ whose $m$-th term is the $m$-th coefficient of the inverse Laurent series $(\mathrm{sharpUnitSeries}\ \ell)^{-1}$, cast from $\mathbb{Q}$ to $\mathbb{C}$, times $\bigl(e^{2\pi i \tau}\bigr)^{m}$ — here $e^{2\pi i\tau}$ is `Function.Periodic.qParam 1 (τ : ℂ)` — is summable with sum the inverse of `sharpUnitFun ℓ τ` in $\mathbb{C}$.
--
--   This records that the formal inverse in $\mathbb{Q}((q))$ of the $q$-expansion of the eta quotient $(\eta(\tau)/\eta(\ell\tau))^{24/\mathrm{sharpIndex}(\ell)}$ converges on the whole upper half-plane to the reciprocal of that modular unit, the inversion being legitimate because the series has a well-defined order ($-e(\ell)$) and the eta quotient does not vanish. It is used in the proof that `sharpUnitSeries ℓ` lies in the field of modular functions attached to the curve, via [`ModularCurve.sharpUnitSeries_mem_modularFunctionField`](thm.html#ModularCurve.sharpUnitSeries_mem_modularFunctionField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_sharpUnitSeries_inv_qParam.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_sharpUnitSeries_inv_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => ((((ModularCurve.sharpUnitSeries ℓ)⁻¹).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((ModularCurve.sharpUnitFun ℓ τ)⁻¹) := by sorry
