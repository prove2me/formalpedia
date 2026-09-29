-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_isIntegral_X
-- name    : ModularCurve.XHDRLevel.isIntegral_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/33cb15fc-c064-5a6d-a770-1ad263f9f3e3
-- title:
--   Integrality of the two-chart integral model X p Γ
-- statement:
--   Let $p$ be a prime and let $\Gamma$ be any subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Assume $hj$: the Laurent series `jqModC ℚ`, namely $q^{-1}$ times the image in $\mathbb{Q}((q))$ of the integral power series `jNum` $= E_4^3\cdot$`dedekindEtaUnitInv` (the $q$-expansion of the modular invariant $j$), belongs to `qExpFunctionFieldC ℚ ⊤`, the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ all quotients `intSeriesC ℚ pf / intSeriesC ℚ pg` arising from two modular forms $f,g$ of one and the same weight $k$ for the full group $\mathrm{SL}_2(\mathbb{Z})$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) together with integral $q$-expansions $pf,pg\in\mathbb{Z}[[q]]$ for them, subject to `intSeriesC ℚ pg ≠ 0`. The conclusion is that the scheme `X p Γ hj` is integral, i.e. nonempty, irreducible and reduced. This scheme is the two-chart integral model over the ring `R p` attached to the $q$-expansion function field `qExpFunctionFieldC ℚ Γ` of level $\Gamma$ and to the element `jAt Γ hj` of that field, glued from the chart algebras `chartAlgFin p Γ hj` and `chartAlgInf p Γ hj` over the middle chart, with structure morphism `toBase p Γ hj`.
--
--   This is the statement that the level-$\Gamma$ two-chart model over $\mathbb{Z}_{(p)}$ — the model of the modular curve built by gluing the $j$-finite and $j^{-1}$-finite charts inside the function field of level $\Gamma$ — is an integral scheme. It is used as an input to the analysis of the models at $p$, being cited by [`ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi`](thm.html#ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_isIntegral_X.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

theorem ModularCurve.XHDRLevel.isIntegral_X
    (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    IsIntegral (X p Γ hj) := by sorry
