-- Prove2me | Theorems.Thm_ModularCurve_evalAtJGen_injective
-- name    : ModularCurve.evalAtJGen_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/6958382e-ee18-5cd3-bb1c-f1a25f5d4e40
-- title:
--   Injectivity of evaluation at the formal j-invariant
-- statement:
--   Work inside the field of Laurent series $\mathbb{Q}((q))$ (formally, `LaurentSeries ℚ`, Hahn series over $\mathbb{Q}$ with value group $\mathbb{Z}$). Let `jNumQ` be the power series over $\mathbb{Q}$ obtained from the integral power series `jNum` by applying the canonical ring homomorphism $\mathbb{Z} \to \mathbb{Q}$ coefficientwise, and let `jq` be the Laurent series $q^{-1} \cdot \mathrm{jNumQ}$, that is, the product of the Hahn series `single (-1) 1` with the image of `jNumQ` in $\mathbb{Q}((q))$. Let $\mathbb{Q}\langle\!\langle \mathrm{jq}\rangle\!\rangle =$ `ℚ⟮jq⟯` be the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `jq`, and let `jGen` denote `jq` regarded as an element of that field. The ring homomorphism `evalAtJGen : Polynomial ℤ →+* ℚ⟮jq⟯` is evaluation at `jGen` of integral polynomials, the coefficients being transported by the canonical map $\mathbb{Z} \to$ `ℚ⟮jq⟯`. The assertion is that this homomorphism is injective: distinct polynomials in $\mathbb{Z}[X]$ have distinct values at `jGen`. Equivalently, `jq` is transcendental over $\mathbb{Q}$ as far as integral polynomials are concerned: no nonzero $p \in \mathbb{Z}[X]$ satisfies $p(\mathrm{jq}) = 0$ in $\mathbb{Q}((q))$.
--
--   This is the formal-Laurent-series form of the transcendence of the $j$-invariant over $\mathbb{Q}$, packaged so that $\mathbb{Z}[X]$ may be identified with the subring $\mathbb{Z}[\mathrm{jq}]$ of `ℚ⟮jq⟯`. It is used in the uniqueness and existence statements for modular polynomial data, [`ModularCurve.modularPolynomialData_phi_unique_of_prime`](thm.html#ModularCurve.modularPolynomialData_phi_unique_of_prime) and [`ModularCurve.nonempty_modularPolynomialData`](thm.html#ModularCurve.nonempty_modularPolynomialData), where two polynomials over $\mathbb{Z}[X]$ with equal images must be shown to coincide.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_evalAtJGen_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.evalAtJGen_injective :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by sorry
