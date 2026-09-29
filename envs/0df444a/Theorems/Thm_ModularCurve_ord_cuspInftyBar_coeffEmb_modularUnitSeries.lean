-- Prove2me | Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
-- name    : ModularCurve.ord_cuspInftyBar_coeffEmb_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/8d565abd-9701-5612-b6e5-df4e39bb782e
-- title:
--   Order of Ogg's unit Δ(q)/Δ(q^ℓ) at ∞̄
-- statement:
--   Let $\ell$ be a nonzero natural number and let `modularUnitSeries ℓ` be the Laurent series over $\mathbb{Q}$ given by $\Delta(q)\,\Delta(q^{\ell})^{-1}$, where $\Delta(q)$ is `deltaSeries`, the product of the monomial $q$ with the power series `dedekindEtaUnitQ` (so $\Delta(q)=q\prod_{n\ge1}(1-q^n)^{24}$), and $\Delta(q^{\ell})$ is its substitution $q\mapsto q^{\ell}$. Assume $hmem$: this series lies in `modularFunctionFieldFull ℓ`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions $j(q^d)$ for the nonzero divisors $d$ of $\ell$. Applying the coefficient ring map `coeffEmb` induced by $\mathbb{Q}\to\overline{\mathbb{Q}}$ carries it into `modularFunctionFieldBar ℓ`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of `modularFunctionFieldFull ℓ`. The assertion is that the order of this element at the place `cuspInftyBar ℓ` — the $q$-adic place of `modularFunctionFieldBar ℓ`, whose valuation subring consists of the elements of nonnegative $q$-order and which is witnessed by the image of $j$ having order $-1$ — equals $1-\ell$ in $\mathbb{Z}$.
--
--   This records the order of Ogg's modular unit $\Delta(z)/\Delta(\ell z)$ on $X_0(\ell)$ at the cusp $\infty$ over $\overline{\mathbb{Q}}$, the basic computation behind the cuspidal divisor $(\ell-1)(0)-(\ell-1)(\infty)$ being principal. It is used by the place-specialisation machinery, in particular in the divisor law for level-one prolongation pairs and in the integrality and residue statements for the inverse unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_cuspInftyBar_coeffEmb_modularUnitSeries (ℓ : ℕ) [NeZero ℓ] (hmem : modularUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) : (cuspInftyBar ℓ).ord (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries ℓ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ : modularFunctionFieldBar ℓ) = 1 - (ℓ : ℤ) := by sorry
