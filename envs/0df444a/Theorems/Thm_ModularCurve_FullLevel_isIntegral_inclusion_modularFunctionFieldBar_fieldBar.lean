-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar
-- name    : ModularCurve.FullLevel.isIntegral_inclusion_modularFunctionFieldBar_fieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/43184b26-f434-5e22-9e70-4da10a98b345
-- title:
--   Integrality of the full-level field over the level-M' floor
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number, and work inside the field $\overline{\mathbb Q}((\mathsf q))$ of Laurent series over an algebraic closure of $\mathbb Q$. Two intermediate fields of $\overline{\mathbb Q}((\mathsf q))/\overline{\mathbb Q}$ are in play: `modularFunctionFieldBar M'`, the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image, under the embedding `coeffEmb`, of the field `modularFunctionFieldFull M'` obtained by adjoining to $\mathbb Q$ the set `divisorExpansions M'`; and `fieldBar q M'`, the subfield generated over $\overline{\mathbb Q}$ by the coefficientwise image of `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction map $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$. Assuming the inclusion `hle` of the first field in the second, the conclusion is that the ring homomorphism underlying the induced inclusion `IntermediateField.inclusion hle` is integral: every element of `fieldBar q M'` satisfies a monic polynomial whose coefficients come from `modularFunctionFieldBar M'`. No hypothesis relating $q$ to $M'$, such as $q \nmid M'$ or $q \ge 5$, is imposed.
--
--   This is the integrality half of the classical statement that the function field of a modular curve of level $q^2M'$ with $H$-structure is a finite extension of the function field of the level-$M'$ curve, both being finite over $\overline{\mathbb Q}(j)$. It is used when a place of the large field is restricted to the smaller one and valuations are compared, in the construction of supersingular tubes and of rational integral cusp-regular evaluation points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.isIntegral_inclusion_modularFunctionFieldBar_fieldBar
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by sorry
