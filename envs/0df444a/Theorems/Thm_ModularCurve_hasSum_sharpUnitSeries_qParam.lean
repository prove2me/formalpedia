-- Prove2me | Theorems.Thm_ModularCurve_hasSum_sharpUnitSeries_qParam
-- name    : ModularCurve.hasSum_sharpUnitSeries_qParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/b0402ce3-5bb7-5155-8018-762c410e28c3
-- title:
--   q-expansion of the sharp eta quotient at ∞
-- statement:
--   Let $\ell$ be a natural number, nonzero, and let $\tau$ be a point of the upper half-plane. Write $q =$ `Function.Periodic.qParam 1 τ`, the nome $e^{2\pi i \tau}$ attached to the period $1$. The theorem asserts that the family indexed by $m \in \mathbb{Z}$ whose $m$-th term is the coefficient of $q^m$ in the formal Laurent series [`ModularCurve.sharpUnitSeries ℓ`](def/ModularCurve_EtaQuotient.html#L85), transported from $\mathbb{Q}$ to $\mathbb{C}$, multiplied by $q^m$, is summable with sum [`ModularCurve.sharpUnitFun ℓ τ`](def/ModularCurve_EtaQuotient.html#L73) (summability being the unconditional `HasSum` over all of $\mathbb{Z}$). Here the analytic value is $\bigl(\eta(\tau)/\eta(M_\ell \cdot \tau)\bigr)^{e}$, where $\eta$ is the Dedekind eta function, $M_\ell$ is the matrix [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21) (the upper triangular element of $\mathrm{GL}_2(\mathbb{R})$ with entries $\ell, 0, 1$, acting on $\tau$ by $\tau \mapsto \ell\tau$), and $e =$ `sharpExp ℓ` $= 24 /$ `sharpIndex ℓ`. The formal side is the product, in the Laurent series field over $\mathbb{Q}$, of the monomial $q^{-n}$ with $n =$ `eisensteinNumerator ℓ` $= (\ell-1)/\gcd(\ell-1,12)$, the power series `etaProdPow ℓ` (the $e$-th power of the integral eta product, with coefficients cast into $\mathbb{Q}$), and the inverse of the image of that power series under `qExpand ℚ ℓ`, the ring endomorphism of Laurent series that multiplies all exponents by $\ell$.
--
--   This identifies the formal Laurent series `sharpUnitSeries ℓ` with the $q$-expansion at the cusp $\infty$ of the eta quotient $(\eta(\tau)/\eta(\ell\tau))^{24/\mathrm{sharpIndex}(\ell)}$, one of the standard modular units on $X_0(\ell)$. It is used by [`ModularCurve.sharpUnitSeries_mem_modularFunctionField`](thm.html#ModularCurve.sharpUnitSeries_mem_modularFunctionField) to exhibit this series as the expansion of an element of the field of modular functions of level $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_sharpUnitSeries_qParam.lean

import Definitions.Def_ModularCurve_EtaQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_sharpUnitSeries_qParam (ℓ : ℕ) [NeZero ℓ] (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((ModularCurve.sharpUnitSeries ℓ).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularCurve.sharpUnitFun ℓ τ) := by sorry
