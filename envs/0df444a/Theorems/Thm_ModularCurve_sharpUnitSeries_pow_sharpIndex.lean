-- Prove2me | Theorems.Thm_ModularCurve_sharpUnitSeries_pow_sharpIndex
-- name    : ModularCurve.sharpUnitSeries_pow_sharpIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/3fa17012-5def-52b5-a191-ae61df449b11
-- title:
--   Sharp eta quotient raised to gcd(ℓ-1,12) gives Δ/Δ_ℓ
-- statement:
--   Let $\ell$ be a natural number, assumed nonzero (the `NeZero ℓ` instance). Put $k(\ell)=$ `sharpIndex ℓ` $=\gcd(\ell-1,12)$ and let $e(\ell)=$ `eisensteinNumerator ℓ` $=(\ell-1)/\gcd(\ell-1,12)$, the quotient being taken in $\mathbb{N}$. Work in the field `LaurentSeries ℚ` of formal Laurent series over $\mathbb{Q}$ (Hahn series with value group $\mathbb{Z}$), and let `qExpand ℚ ℓ` be the ring homomorphism of `LaurentSeries ℚ` that multiplies all exponents by $\ell$, i.e. the substitution $q\mapsto q^{\ell}$. The series `sharpUnitSeries ℓ` is the product of the monomial $q^{-e(\ell)}$, the Laurent series attached to the power series `etaProdPow ℓ` $=$ the image in $\mathbb{Q}[[q]]$ of `etaProd` raised to the exponent `sharpExp ℓ`, and the inverse of the image of that same Laurent series under `qExpand ℚ ℓ`. The series `modularUnitSeries ℓ` is `deltaSeries` times the inverse of `deltaSeriesN ℓ` $=$ `qExpand ℚ ℓ` applied to `deltaSeries`, where `deltaSeries` $= q\cdot$ (the Laurent series attached to the power series `dedekindEtaUnitQ`). The assertion is the identity $(\mathrm{sharpUnitSeries}\,\ell)^{k(\ell)} = \mathrm{modularUnitSeries}\,\ell$ in `LaurentSeries ℚ`.
--
--   This is the formal $q$-expansion form of the classical fact that the $\gcd(\ell-1,12)$-th power of the sharp eta quotient $(\eta(\tau)/\eta(\ell\tau))^{e(\ell)}$, up to the normalising power of $q$, equals Ogg's modular unit $\Delta(\tau)/\Delta(\ell\tau)$ on $X_0(\ell)$. It is used in the treatment of the $q$-expansions of the sharp unit series, in particular by the summability statements [`ModularCurve.hasSum_sharpUnitSeries_qParam`](thm.html#ModularCurve.hasSum_sharpUnitSeries_qParam), [`ModularCurve.hasSum_sharpUnitSeries_inv_qParam`](thm.html#ModularCurve.hasSum_sharpUnitSeries_inv_qParam) and [`ModularCurve.hasSum_smul_sharpUnitSeries_inv_qParam`](thm.html#ModularCurve.hasSum_smul_sharpUnitSeries_inv_qParam).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sharpUnitSeries_pow_sharpIndex.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.sharpUnitSeries_pow_sharpIndex (ℓ : ℕ) [NeZero ℓ] : ModularCurve.sharpUnitSeries ℓ ^ ModularCurve.sharpIndex ℓ = ModularCurve.modularUnitSeries ℓ := by sorry
