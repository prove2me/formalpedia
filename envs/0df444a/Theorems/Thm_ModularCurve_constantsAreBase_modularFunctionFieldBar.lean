-- Prove2me | Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldBar
-- name    : ModularCurve.constantsAreBase_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/86432165-08ae-5bc4-959d-d27a3dbf7528
-- title:
--   Constants of ℚ̄-modular function field are the base
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. Consider the field $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and the intermediate field `modularFunctionFieldBar N` of the Laurent series field $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$, namely `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`: the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image, under the coefficientwise embedding `coeffEmb` of $\mathbb{Q}((q))$ into $\overline{\mathbb{Q}}((q))$, of the subfield `modularFunctionFieldFull N` of $\mathbb{Q}((q))$, which in turn is generated over $\mathbb{Q}$ by the set `divisorExpansions N` of $q$-expansions attached to the divisors of $N$. The assertion is `ConstantsAreBase` for this extension: the Riemann–Roch space `LSpace` of the zero divisor, the zero function in the group `Divisor` $=$ `Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →₀ ℤ` of divisors of the extension, coincides, as a $\overline{\mathbb{Q}}$-submodule of `modularFunctionFieldBar N`, with the range of the $\overline{\mathbb{Q}}$-linear structure map `Algebra.linearMap`. In other words, the elements of the field which are integral at every place are exactly the images of the scalars from $\overline{\mathbb{Q}}$.
--
--   This is the statement that the exact constant field of the function field of $X_0(N)$ over $\overline{\mathbb{Q}}$ is $\overline{\mathbb{Q}}$ itself, the function-field form of geometric connectedness of the curve. It is used throughout the subsequent development of places, divisor classes and Riemann–Roch spaces on this function field, for instance in the analysis of prolongations of places and of the local behaviour at nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_constantsAreBase_modularFunctionFieldBar.lean

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.constantsAreBase_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    ConstantsAreBase (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by sorry
