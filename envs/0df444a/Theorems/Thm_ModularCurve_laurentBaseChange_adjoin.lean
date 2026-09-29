-- Prove2me | Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
-- name    : ModularCurve.laurentBaseChange_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3207623f-def9-5013-a768-e131bf7989de
-- title:
--   Base change of a Laurent-series subfield commutes with adjunction
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $S$ be an arbitrary subset of the field $\mathbb{Q}((q))$ of formal Laurent series over $\mathbb{Q}$. Write $\iota_L =$ [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ obtained by applying the structure map $\mathbb{Q} \to L$ to each coefficient (the instance of [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) at $\mathrm{algebraMap}\ \mathbb{Q}\ L$), and recall that for an intermediate field $F_0$ of $\mathbb{Q}((q))/\mathbb{Q}$ the base change [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) is by definition the intermediate field of $L((q))/L$ generated over $L$ by the set-theoretic image $\iota_L(F_0)$. The theorem asserts the equality of intermediate fields of $L((q))/L$ $$\mathrm{laurentBaseChange}\ L\ \bigl(\mathbb{Q}(S)\bigr) = L\bigl(\iota_L(S)\bigr),$$ that is, adjoining to $L$ the coefficientwise image of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by $S$ gives the same subfield of $L((q))$ as adjoining to $L$ the image $\iota_L(S)$ of the generating set itself.
--
--   This is the compatibility of the coefficient-extension operation on subfields of formal Laurent series with field adjunction: base change may be computed on generators. It is used throughout the treatment of $q$-expansions of modular functions, where function fields such as $\mathbb{Q}(j(q^d) : d \mid M)$ are given by explicit generators and must be compared with their base changes to a larger field of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurentBaseChange_adjoin.lean

import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.laurentBaseChange_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) : ModularCurve.laurentBaseChange L (IntermediateField.adjoin ℚ S) = IntermediateField.adjoin L (ModularCurve.coeffEmb L '' S) := by sorry
