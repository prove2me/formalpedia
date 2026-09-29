-- Prove2me | Theorems.Thm_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
-- name    : ModularCurve.order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/14fb4e14-04f4-5d03-a246-f71c421c8880
-- title:
--   Germs at the cusp ∞ have pole-free q-expansions
-- statement:
--   Fix $p \in \mathbb{N}$ with $p \neq 0$ and let $F =$ [`ModularCurve.modularFunctionFieldFull p`](def/ModularCurve_X0.html#L305) be the intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of series $\mathrm{qExpand}\,\mathbb{Q}\,d\,jq$ for the nonzero divisors $d$ of $p$. Let $M$ be an [`AlgebraicCurve.CurveModel`](def/AlgebraicCurve_CurveModel.html#L23) of $F$ over $\mathbb{Q}$: an integral scheme $M.C$ together with a proper morphism to $\operatorname{Spec}\mathbb{Q}$ that is smooth of relative dimension $1$, a ring isomorphism $M.\mathrm{ffEquiv} : F \cong K(M.C)$ compatible with the structure maps from $\mathbb{Q}$, a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $M.C$ onto the places of $F/\mathbb{Q}$ (valuation subrings of $F$, proper, containing $\mathbb{Q}$, with principal ideal valuation ring), the axiom that for each closed point $x$ the image in $F$ of the stalk $\mathcal{O}_{M.C,x}$ under $M.\mathrm{ffEquiv}^{-1}$ is exactly the valuation subring of $M.\mathrm{placeOfPoint}(x)$, and the axiom that every finite set of points of $M.C$ lies in an affine open. Let $x$ be a closed point whose attached place is the $q$-adic cusp $\mathrm{cuspInftyFull}\,p$, whose valuation subring is the ring of elements of $F$ of non-negative $q$-order. Then for every germ $g \in \mathcal{O}_{M.C,x}$, the Laurent series in $\mathbb{Q}((q))$ obtained from the image of $g$ in $K(M.C)$ under $M.\mathrm{ffEquiv}^{-1}$ has order $\geq 0$, i.e. lies in $\mathbb{Q}[[q]]$ (the case $g = 0$ being covered by the convention $\operatorname{ord}(0) = 0$).
--
--   This is the function-field form of the elementary fact that a modular function regular at the cusp $\infty$ has a $q$-expansion with no pole. It is the starting point for the analysis of cusp expansions on a model of the full modular function field, and is used by the results identifying germs at the cusp with power series, characterising units by order $0$, and producing a local parameter from $jq^{-1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull.lean

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry

theorem ModularCurve.order_ffEquiv_symm_nonneg_of_placeOfPoint_eq_cuspInftyFull
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (g : M.C.presheaf.stalk x.1) :
    0 ≤ (((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ)).order := by sorry
