-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_evalAtJ_injective
-- name    : ModularCurve.PhiGen.evalAtJ_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/4d325b73-db93-53aa-896c-9b9b539ab24a
-- title:
--   Injectivity of evaluation at j(q)
-- statement:
--   The assertion concerns the ring homomorphism `evalAtJ` from the polynomial ring $\mathbb{Z}[X]$ to the field of formal Laurent series $\mathbb{Q}((q))$, defined as the $\mathbb{Z}$-algebra evaluation map sending a polynomial $P$ to $P(\mathtt{jq})$, where `jq` is the fixed Laurent series over $\mathbb{Q}$ playing the role of the $q$-expansion of the modular $j$-invariant, viewed as a ring homomorphism. The theorem takes no arguments and no hypotheses: it states that this map is injective as a function, i.e. that a polynomial with integer coefficients which vanishes after substituting the Laurent series `jq` for its variable is the zero polynomial. Equivalently, the element `jq` of $\mathbb{Q}((q))$ satisfies no nontrivial polynomial relation with integer coefficients; since $\mathbb{Q}$ is the fraction field of $\mathbb{Z}$, this amounts to the transcendence of `jq` over $\mathbb{Q}$ inside the Laurent series field.
--
--   This is the basic transcendence statement underlying the use of $q$-expansions to pin down polynomial identities between modular functions: a relation among $q$-expansions can be read back as an identity of polynomials. It is used by the results on `ModularPolynomialData`, among them [`ModularCurve.ModularPolynomialData.eq_all`](thm.html#ModularCurve.ModularPolynomialData.eq_all), [`ModularCurve.ModularPolynomialData.eq_of_prime`](thm.html#ModularCurve.ModularPolynomialData.eq_of_prime) and [`ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare`](thm.html#ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare), where modular polynomials are characterised through their behaviour on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_evalAtJ_injective.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.evalAtJ_injective : Function.Injective evalAtJ := by sorry
