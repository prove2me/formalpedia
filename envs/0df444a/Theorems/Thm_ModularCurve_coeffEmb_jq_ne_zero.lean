-- Prove2me | Theorems.Thm_ModularCurve_coeffEmb_jq_ne_zero
-- name    : ModularCurve.coeffEmb_jq_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/5feb12d1-7cf7-507f-adac-c48e499fba50
-- title:
--   Non-vanishing of j(q) over a characteristic-zero field
-- statement:
--   Let $L$ be a field of characteristic zero, so that $L$ is canonically a $\mathbb{Q}$-algebra. Write [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) for the ring homomorphism $\mathbb{Q}((q)) \to L((q))$ on Laurent series (Hahn series over $\mathbb{Z}$ with values in the base ring) obtained by applying the structure map $\mathbb{Q} \to L$ to each coefficient, i.e. [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) of `algebraMap ℚ L`. Write [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) for the element of $\mathbb{Q}((q))$ given by the product of the Hahn series $q^{-1}$, the monomial `HahnSeries.single (-1) 1`, with the Laurent series attached to the power series [`ModularCurve.jNumQ`](def/ModularCurve_X0.html#L149), the coefficientwise image in $\mathbb{Q}[[q]]$ under $\mathbb{Z} \to \mathbb{Q}$ of the integral power series [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142). The assertion is that the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) is a non-zero element of $L((q))$; concretely, the $q$-expansion $q^{-1} + 744 + \cdots$ of the modular $j$-invariant, read in $L((q))$, does not vanish.
--
--   This records that the $q$-expansion of $j$ remains non-zero after extension of the coefficient field from $\mathbb{Q}$ to an arbitrary field of characteristic zero. It supplies the non-vanishing hypothesis on $j$ required when setting up the two-chart description of modular curves, and is invoked in the construction of charts, poles and nodes over level fields in the full-level analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffEmb_jq_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeffEmb_jq_ne_zero
    (L : Type) [Field L] [CharZero L] : ModularCurve.coeffEmb L ModularCurve.jq ≠ 0 := by sorry
