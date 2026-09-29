-- Prove2me | Theorems.Thm_ModularCurve_coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
-- name    : ModularCurve.coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/21d9c391-f06d-52a9-b7a2-b4bd0449d5fb
-- title:
--   Vanishing constant term of q-expansions at the cusp ∞
-- statement:
--   Let $p$ be a nonzero natural number and let $F =$ [`ModularCurve.modularFunctionFieldFull p`](def/ModularCurve_X0.html#L305) be the intermediate field of $\mathbb{Q} \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the set of series $\mathrm{qExpand}\,\mathbb{Q}\,d\,\mathrm{jq}$ for the nonzero divisors $d$ of $p$. Let $M$ be a `CurveModel` of $F$ over $\mathbb{Q}$: an integral scheme $M.C$ together with a proper, smooth of relative dimension $1$ morphism to $\operatorname{Spec}\mathbb{Q}$, a ring isomorphism $M.\mathrm{ffEquiv} : F \simeq M.C.\mathrm{functionField}$ over $\mathbb{Q}$, and a bijection $M.\mathrm{placeOfPoint}$ from the closed points of $M.C$ onto the places of $F$ over $\mathbb{Q}$ (valuation subrings of $F$ containing $\mathbb{Q}$, proper, with principal ideals), subject to the requirement that for each closed point $x$ the image of the stalk $\mathcal{O}_{M.C,x}$ in $F$ under $M.\mathrm{ffEquiv}^{-1}$ composed with the inclusion into the function field is exactly the valuation subring of $M.\mathrm{placeOfPoint}(x)$, and to the condition that every finite set of points lies in an affine open. Let $x$ be a closed point of $M.C$ with $M.\mathrm{placeOfPoint}(x) = \mathrm{cuspInftyFull}\,p$, the place of $F$ whose valuation subring is $\mathrm{qIntegersBar}\,\mathbb{Q}\,F$ (constructed using $\mathrm{jq}$, of $q$-order $-1$, as witness). Then for every germ $g$ in the maximal ideal of the local ring $\mathcal{O}_{M.C,x}$, the Laurent series in $\mathrm{LaurentSeries}\,\mathbb{Q}$ obtained from $g$ by mapping it into the function field and transporting back along $M.\mathrm{ffEquiv}^{-1}$ has coefficient $0$ in degree $0$.
--
--   This is the function-field form of the statement that a function on a model of the modular curve which is regular and vanishing at the cusp $\infty$ has a $q$-expansion with zero constant term, the constant term being the value of the function at the cusp. It is used in the identification of the local parameter at the cusp, feeding the results that produce a power series representative of the $q$-expansion of a germ at the cusp and that exhibit a unit comparison with $\mathrm{jq}^{-1}$ on the cusp section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull.lean

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry

theorem ModularCurve.coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (g : M.C.presheaf.stalk x.1)
    (hg : g ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) :
    (((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ)).coeff 0 = 0 := by sorry
